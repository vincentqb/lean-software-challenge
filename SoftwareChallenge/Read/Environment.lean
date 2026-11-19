module

public meta import Lean
public meta import SoftwareChallenge.CoreCode.Facts
public meta import SoftwareChallenge.CoreCode.Rules.Statement
public meta import SoftwareChallenge.Read.Source
meta import all Lean.Environment

public section
meta section

open Lean

namespace SoftwareChallenge.Read

def libraryDir (lake : LakeFacts) : System.FilePath :=
  System.FilePath.mk lake.packageDir / ".lake" / "build" / "lib" / "lean"

def oleanOf (lake : LakeFacts) (module : Name) : System.FilePath :=
  modToFilePath (libraryDir lake) module "olean"

private def present (files : List System.FilePath) : IO (Array System.FilePath) := do
  let mut found := #[]
  for file in files do
    unless ← file.pathExists do break
    found := found.push file
  return found

def oleanParts (olean : System.FilePath) : List System.FilePath :=
  [olean, olean.addExtension "server", olean.addExtension "private"]

def artifactsOf (lake : LakeFacts) (module : Name) : IO (Option ImportArtifacts) := do
  let olean := oleanOf lake module
  unless ← olean.pathExists do return none
  let parts ← present (oleanParts olean)
  let ir ← present [olean.withExtension "ir.sig", olean.withExtension "ir"]
  return some (.ofArrays #[parts, ir])

def distinct (names : Array Name) : Array Name :=
  names.foldl (fun kept name => if kept.contains name then kept else kept.push name) #[]

def packageModules (lake : LakeFacts) : Array Name :=
  distinct (lake.modules.map (·.module) ++ lake.challengeCandidates.map (·.module) ++ lake.exeRoots)

def catalog (lake : LakeFacts) (challenge : Name) : Array Name :=
  distinct ((lake.modules.map (·.module) ++ lake.exeRoots).filter (· != challenge))

def fileOf (lake : LakeFacts) (module : Name) : String :=
  (((lake.modules ++ lake.challengeCandidates).find? (·.module == module)).map (·.file)).getD (sourcePath module)

structure Imported where
  env : Environment
  trimmed : NameMap ModuleData

def Imported.compiled? (imported : Imported) (module : Name) : Option (ModuleIdx × ModuleData) := do
  let (index, data) ← moduleData? imported.env module
  return (index, (imported.trimmed.find? module).getD data)

def partsMessage (lake : LakeFacts) (module : Name) (missing : System.FilePath) (next : Next) : String :=
  s!"{fileOf lake module}:1: the compiled {module} lacks {missing}, which `lake build` writes for every `module` \
    file, so the step cannot read the declarations and proofs of {module}, as when a build cache ships only public \
    .olean files. Run `lake build {module}` so that Lake rebuilds it, then run `{next.command}`."

private def requireParts (lake : LakeFacts) (state : ImportState) (next : Next) : IO Unit := do
  for name in packageModules lake do
    let some module := state.moduleNameMap[name]? | continue
    unless module.hasData && module.mainModule?.isNone do continue
    let some missing ← (oleanParts (oleanOf lake name)).findM? fun part => return !(← part.pathExists)
      | continue
    throw <| .userError (partsMessage lake name missing next)

private def mainPart (module : ImportedModule) : Nat :=
  (if module.importAll && module.publicModule?.any (·.isModule) then OLeanLevel.private else .exported).ctorIdx

private def without (data : ModuleData) (dropped : NameSet) : ModuleData :=
  let kept := (data.constNames.zip data.constants).filter (!dropped.contains ·.1)
  { data with constNames := kept.map (·.1), constants := kept.map (·.2) }

structure Clash where
  name : Name
  kept : Name
  dropped : Name

private def withoutClashes (state : ImportState) (roots : Array Name) :
    ImportState × NameMap ModuleData × Array Clash := Id.run do
  let mut state := state
  let mut trimmed := {}
  let mut clashes := #[]
  let mut seen : NameSet := {}
  let mut owners : Std.HashMap Name Name := {}
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in roots ++ state.moduleNames do
    if seen.contains name then continue
    seen := seen.insert name
    let some module := state.moduleNameMap[name]? | continue
    let some data := module.mainModule? | continue
    let mut dropped : NameSet := {}
    for constant in data.constNames, info in data.constants do
      match owners[constant]?, constants[constant]? with
      | some owner, some kept =>
        unless subsumesInfo constants info kept || subsumesInfo constants kept info do
          dropped := dropped.insert constant
          clashes := clashes.push { name := constant, kept := owner, dropped := name }
      | _, _ =>
        owners := owners.insert constant name
        constants := constants.insert constant info
    if module.hasData && !dropped.isEmpty then
      trimmed := trimmed.insert name data
      let parts := module.parts.modify (mainPart module) fun (_, region) => (without data dropped, region)
      state := { state with moduleNameMap := state.moduleNameMap.insert name { module with parts } }
  return (state, trimmed, clashes)

def clashMessage (lake : LakeFacts) (imported : Imported) (clash : Clash) (next : Next) : String :=
  let inPackage := (packageModules lake).contains
  let module := if inPackage clash.dropped then clash.dropped else clash.kept
  let ranges := (imported.compiled? module).bind fun (index, _) => rangesIn imported.env index clash.name
  let line := (ranges.map fun (found : DeclarationRanges) => found.range.pos.line).getD 1
  let place := if inPackage module then s!"{fileOf lake module}:{line}"
    else s!"{lake.configFiles[0]?.getD "lakefile.lean"}:1"
  let fix := if inPackage module then s!"Rename {clash.name} in {fileOf lake module}"
    else s!"Import at most one of {clash.kept} and {clash.dropped} in the package's modules"
  s!"{place}: {clash.name} is declared both in {clash.kept} and in {clash.dropped}, which no module imports \
    together, so the step cannot read the package's modules in one environment, as it must to judge them. {fix}, \
    then run `{next.command}`."

def importEnvironment (lake : LakeFacts) (roots : Array Name) (next : Next) : IO Imported := do
  let arts ← (packageModules lake).foldlM (init := ({} : NameMap ImportArtifacts)) fun arts module => do
    return match ← artifactsOf lake module with
      | some found => arts.insert module found
      | none => arts
  let imports := roots.map ({ module := · })
  unsafe enableInitializersExecution
  withImporting do
    let (_, state) ← (importModulesCore imports (arts := arts)).run
    requireParts lake state next
    let finalize := fun state => finalizeImport state imports {} (leakEnv := false) (loadExts := true)
    try return { env := ← finalize state, trimmed := {} }
    catch _ =>
      let (state, trimmed, clashes) := withoutClashes state roots
      let imported : Imported := { env := ← finalize state, trimmed }
      let outside := clashes.filter fun clash =>
        !(packageModules lake).contains clash.kept || !(packageModules lake).contains clash.dropped
      unless outside.isEmpty do
        throw <| .userError ("\n".intercalate (outside.map (clashMessage lake imported · next)).toList)
      return imported

def challengeEnv (lake : LakeFacts) (challenge : Name) (next : Next) : IO Imported :=
  importEnvironment lake (Statement.statementRoots lake challenge) next

def catalogEnv (lake : LakeFacts) (challenge : Name) (next : Next) : IO Imported :=
  importEnvironment lake (catalog lake challenge) next

def runIn {α : Type} (env : Environment) (action : MetaM α) : IO α := do
  let (result, _) ← (action.run' {} {}).toIO
    { fileName := "<lean-software-challenge>", fileMap := default, maxHeartbeats := 0 }
    { env := env.setExporting false }
  return result

end SoftwareChallenge.Read

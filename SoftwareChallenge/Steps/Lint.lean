module

public meta import SoftwareChallenge.Read
public meta import SoftwareChallenge.CoreCode.Rules.Lint
public meta import SoftwareChallenge.Steps.Statement

public section
meta section

open Lean

namespace SoftwareChallenge.Steps.Lint

def run (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let result := SoftwareChallenge.Lint.run (← Read.readFacts lake .lint)
  IO.println ("\n".intercalate result.report.toList)
  return result.code

def importers (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let some candidate := Read.challengeOf? lake | return 3
  let facts : Facts := { (default : Facts) with lake, challenge := Read.emptyChallenge candidate.module candidate.file }
  let lines ← challengeImports lake .lint
  if lines.isEmpty then return 3
  IO.println (errorListing (lines.map fun line => Report.item ((Lint.Error.importsChallenge line).message facts))
    "lake lint" .lint)
  return 1

def firstLinted (closures : Array (Name × Array Name)) : Array (Name × NameSet) := Id.run do
  let mut linted : NameSet := {}
  let mut found := #[]
  for (top, closure) in closures do
    let fresh := closure.filter fun module => top.getRoot.isPrefixOf module && !linted.contains module
    linted := fresh.foldl NameSet.insert linted
    found := found.push (top, fresh.foldl NameSet.insert {})
  return found

@[noinline] def isModuleData (data : ModuleData) : BaseIO Bool := return data.isModule

def importLevel (modules : Array Name) : IO OLeanLevel := do
  for module in modules do
    let (data, region) ← readModuleData (← findOLean module)
    let isModule ← isModuleData data
    unsafe region.free
    unless isModule do return .private
  return .server

def siteOf : Doc.DeferredCheckSite → String
  | .decl name => s!"the docstring of `{name}`"
  | .moduleDoc index => s!"module docstring #{index + 1}"

def lintTogether (sources : SearchPath) (modules : Array Name) : CoreM Bool := do
  let env ← getEnv
  let linters ← Linter.EnvLinter.getEnvLinters
  let mut clean := true
  for (module, fresh) in firstLinted (modules.map fun module => (module, Read.importClosure env module)) do
    if linters.isEmpty then
      IO.println s!"-- No environment linters were run for {module}."
    else
      let decls := (← Linter.EnvLinter.getDeclsInPackage module.getRoot).filter fun decl =>
        (env.getModuleIdxFor? decl).any (fresh.contains env.header.moduleNames[·.toNat]!)
      let results ← Linter.EnvLinter.lintCore decls linters
      if results.any (!·.2.isEmpty) then
        clean := false
        IO.print (← (← Linter.EnvLinter.formatLinterResults results decls (groupByFilename := true)
          (useErrorFormat := true) s!"in {module}" linters.size).toString)
      else
        IO.println s!"-- Environment linting passed for {module}."
    let checks ← Doc.DeferredCheck.run fresh.contains fun check =>
      return Linter.getLinterValue linter.doc.deferred (← check.options.toLinterOptions)
    for (found, check, message) in checks do
      clean := false
      let context := if check.sourceString.isEmpty then "" else s!" ({check.sourceString})"
      let place := match ← sources.findWithExt "lean" found with
        | some file => s!"{file}: error: in"
        | none => s!"error: in module `{found}`, in"
      IO.eprintln s!"{place} {siteOf check.site}{context}: {← message.toString}"
  return clean

def environmentLinters (lake : LakeFacts) (lakeCommand : String) (targets : List String) : IO Bool := do
  if targets.isEmpty then return true
  let built ← IO.Process.output { cmd := lakeCommand, cwd := lake.packageDir
                                  args := #["build", "--log-level=error"] ++ (targets.map ("+" ++ ·)).toArray }
  unless built.exitCode == 0 do
    IO.print built.stdout
    IO.eprint built.stderr
    return false
  let modules := targets.toArray.map String.toName
  unsafe enableInitializersExecution
  let imports := (modules.map ({ module := · })).push { module := `Lean.Linter.EnvLinter }
  let env ← try importModules imports {} (trustLevel := 1024) (loadExts := true) (level := ← importLevel modules)
    catch failure => do
      IO.eprintln s!"Lean's linters cannot load the package's top modules {", ".intercalate targets} together: \
        {failure}. When Lean reports a name already declared, two of those modules declare it, or two define \
        `main`: rename one of them, then run `lake lint`."
      return false
  let (clean, _) ← (lintTogether (← getSrcSearchPath) modules).toIO { fileName := "", fileMap := default } { env }
  (← IO.getStdout).flush
  return clean

def lintTargets (lake : LakeFacts) : IO (List String) := do
  let imported ← lake.modules.flatMapM fun source => do
    return (← Read.importLines source.module source.file (← Read.readSource lake source.file .lint)).map (·.fact.name)
  let (roots, others) := (lake.modules.filter (!imported.contains ·.module)).partition
    (lake.defaultExeRoots.contains ·.module)
  return (others ++ roots).toList.map (·.module.toString)

def drive (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let lakeCommand := (← IO.getEnv "LAKE").getD "lake"
  let clean ← environmentLinters lake lakeCommand (← lintTargets lake)
  let ran := (lakeFile.parent.getD ".") / "lint.ran"
  if ← ran.pathExists then IO.FS.removeFile ran
  discard <| (← IO.Process.spawn
    { cmd := lakeCommand, args := #["build", "--log-level=error", ":softwareChallenge"], cwd := lake.packageDir }).wait
  let status := (lakeFile.parent.getD ".") / "lint.status"
  let code ← if (← ran.pathExists) && (← status.pathExists) then do
      let code := (((← IO.FS.readFile status).trimAscii.toString.toNat?).getD 3).toUInt32
      let report := (lakeFile.parent.getD ".") / "lint.out"
      if (code == 0 || code == 2) && (← report.pathExists) then IO.print (← IO.FS.readFile report)
      pure code
    else do
      IO.eprintln "lake lint could not build the package's modules, as printed above, so the audit did not run. Fix \
        each error above; when the linker reports a `multiple definition`, two modules define the same name, or two \
        executables define `main`, so rename one of them. Then run `lake lint`."
      pure 1
  unless clean do
    IO.eprintln "Lean's linters report the problems printed above, so the solution is not clean. Fix each at the \
      file and line it names, then run `lake lint`."
  return if clean || code == 3 then code else 1

end SoftwareChallenge.Steps.Lint

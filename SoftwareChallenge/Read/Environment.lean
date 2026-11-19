module

public meta import Lean
public meta import SoftwareChallenge.CoreCode.Facts

public section
meta section

open Lean

namespace SoftwareChallenge.Read

def libraryDir (lake : LakeFacts) : System.FilePath :=
  System.FilePath.mk lake.packageDir / ".lake" / "build" / "lib" / "lean"

private def present (files : List System.FilePath) : IO (Array System.FilePath) := do
  let mut found := #[]
  for file in files do
    unless ← file.pathExists do break
    found := found.push file
  return found

def artifactsOf (lake : LakeFacts) (module : Name) : IO (Option ImportArtifacts) := do
  let olean := modToFilePath (libraryDir lake) module "olean"
  unless ← olean.pathExists do return none
  let parts ← present [olean, olean.addExtension "server", olean.addExtension "private"]
  let ir ← present [olean.withExtension "ir.sig", olean.withExtension "ir"]
  return some (.ofArrays #[parts, ir])

def distinct (names : Array Name) : Array Name :=
  names.foldl (fun kept name => if kept.contains name then kept else kept.push name) #[]

def packageModules (lake : LakeFacts) : Array Name :=
  distinct (lake.modules.map (·.module) ++ lake.challengeCandidates.map (·.module) ++ lake.exeRoots)

def catalog (lake : LakeFacts) (challenge : Name) : Array Name :=
  distinct ((lake.modules.map (·.module) ++ lake.exeRoots).filter (· != challenge))

def importEnvironment (lake : LakeFacts) (roots : Array Name) : IO Environment := do
  let arts ← (packageModules lake).foldlM (init := ({} : NameMap ImportArtifacts)) fun arts module => do
    return match ← artifactsOf lake module with
      | some found => arts.insert module found
      | none => arts
  unsafe enableInitializersExecution
  importModules (roots.map ({ module := · })) {} (loadExts := true) (arts := arts)

def challengeEnv (lake : LakeFacts) (challenge : Name) : IO Environment :=
  importEnvironment lake #[challenge]

def catalogEnv (lake : LakeFacts) (challenge : Name) : IO Environment :=
  importEnvironment lake (catalog lake challenge)

def runIn {α : Type} (env : Environment) (action : MetaM α) : IO α := do
  let (result, _) ← (action.run' {} {}).toIO
    { fileName := "<lean-software-challenge>", fileMap := default, maxHeartbeats := 0 }
    { env := env.setExporting false }
  return result

end SoftwareChallenge.Read

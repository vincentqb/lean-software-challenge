module

public meta import Lean.Data.Json
public meta import SoftwareChallenge.CoreSpec.Facts
public meta import SoftwareChallenge.Read.Source

public section
meta section

open Lean

namespace SoftwareChallenge

deriving instance ToJson, FromJson for Place
deriving instance FromJson for SourceFact
deriving instance FromJson for PackageFact
deriving instance FromJson for OwnTestKind

namespace Read

structure LakeTest where
  name : String
  kind : OwnTestKind
  deriving FromJson

structure LakeConfig where
  packageDir : String
  configFiles : Array String
  modules : Array SourceFact
  challengeCandidates : Array SourceFact
  defaultExeRoots : Array Name
  packages : Array PackageFact
  defaultTargets : Array Name
  builtinLint : Bool
  lintDriver : String
  testDriver : String
  testDriverArgs : Array String
  ownTests : Array LakeTest
  inputs : Array String
  deriving FromJson

def lexical (path : String) : String :=
  "/".intercalate <| (path.splitOn "/").foldl (init := []) fun parts part =>
    if part == "." then parts else if part == ".." && parts.length > 1 then parts.dropLast else parts ++ [part]

def LakeTest.declaredIn (test : LakeTest) (line : String) : Bool :=
  let keyword := match test.kind with
    | .script => "script "
    | .library => "lean_lib "
    | .executable => "lean_exe "
  line.startsWith keyword && ((line.drop keyword.length).toString.splitOn " ").head?.any
    ([test.name, s!"«{test.name}»"].contains ·)

def LakeConfig.facts (lake : LakeConfig) (config : String) : LakeFacts :=
  let file := lake.configFiles[0]?.getD "lakefile.lean"
  let place := fun (holds : String → Bool) =>
    ({ file, line := (((config.splitOn "\n").findIdx? holds).map (· + 1)).getD 1 } : Place)
  { packageDir := lake.packageDir, configFiles := lake.configFiles, modules := lake.modules
    challengeCandidates := lake.challengeCandidates, defaultExeRoots := lake.defaultExeRoots
    packages := lake.packages.map fun package => { package with configured := lexical package.configured }
    defaultTargets := lake.defaultTargets, lintDriver := lake.lintDriver, testDriver := lake.testDriver
    builtinLint := if lake.builtinLint then some (place (·.contains "builtinLint")) else none
    testDriverArgs := lake.testDriverArgs, testDriverArgsPlace := place (·.contains "testDriverArgs")
    ownTests := lake.ownTests.map fun test => { name := test.name, kind := test.kind, place := place test.declaredIn }
    inputs := lake.inputs }

def parseLake (text : String) : Except String LakeConfig := do
  fromJson? (← Json.parse text)

def rebuildThenRun (next : Next) : String :=
  if next == .build then "run `lake build`" else s!"run `lake build`, then run `{next.command}`"

def loadLake (path : System.FilePath) (next : Next) : IO LakeFacts := do
  let text ← try IO.FS.readFile path catch failure =>
    throw <| .userError s!"{path}:1: the step cannot read it ({failure}), so it does not know the package's modules, \
      files, and settings. `lake build` writes it: {rebuildThenRun next}."
  match parseLake text with
  | .ok lake =>
    let config := System.FilePath.mk lake.packageDir / lake.configFiles[0]?.getD "lakefile.lean"
    return lake.facts (← if ← config.pathExists then IO.FS.readFile config else pure "")
  | .error problem =>
    throw <| .userError s!"{path}:1: it is not the JSON object of Lake facts that `lake build` writes ({problem}), \
      so the step does not know the package's modules, files, and settings. Delete {path} and \
      {rebuildThenRun next}."

end SoftwareChallenge.Read

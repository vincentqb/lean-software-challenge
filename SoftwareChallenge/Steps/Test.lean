module

public meta import SoftwareChallenge.Read
public meta import SoftwareChallenge.CoreCode.Rules.Test
public meta import SoftwareChallenge.CoreCode.Report.Report
public meta import SoftwareChallenge.Steps.Checks

public section
meta section

open Lean

namespace SoftwareChallenge.Steps.Test

def lakeCommand : IO String := return (← IO.getEnv "LAKE").getD "lake"

def runnerSource (modules : Array SourceFact) (out : System.FilePath) : String :=
  let listed := ", ".intercalate (modules.map fun source =>
    s!"(`{source.module}, {(toJson source.file).compress})").toList
  "\n".intercalate (["import SoftwareChallenge.Steps.Checks"] ++ (modules.map (s!"import {·.module}")).toList ++
    [s!"run_cmd SoftwareChallenge.Steps.Checks.run {(toJson out.toString).compress} #[{listed}]", ""])

def checkGroups (lake : LakeFacts) : Array (Array SourceFact) :=
  let roots := lake.modules.filter (lake.defaultExeRoots.contains ·.module)
  if roots.size ≤ 1 then #[lake.modules] else
    let first := ((roots.find? (Role.ofName ·.module == .worldCode)).orElse fun _ => roots[0]?).getD default
    let others := roots.filter (·.module != first.module)
    #[lake.modules.filter fun source => !others.any (·.module == source.module)] ++ others.map (#[·])

def runGroup (lake : LakeFacts) (loads : Array String) (dir : System.FilePath) (index : Nat)
    (modules : Array SourceFact) : IO (Option Checks.Ran × IO.Process.Output) := do
  let suffix := if index == 0 then "" else toString index
  let runner := dir / s!"Checks{suffix}.lean"
  let out := dir / s!"checks{suffix}.json"
  if ← out.pathExists then IO.FS.removeFile out
  IO.FS.writeFile runner (runnerSource modules out)
  let output ← IO.Process.output { cmd := ← lakeCommand, args := #["lean", runner.toString, "--"] ++ loads
                                   cwd := lake.packageDir }
  unless ← out.pathExists do return (none, output)
  return ((Json.parse (← IO.FS.readFile out) >>= fromJson?).toOption, output)

def runChecks (lake : LakeFacts) (loads : Array String) (dir : System.FilePath) :
    IO (Option Checks.Ran × IO.Process.Output) := do
  let mut ran : Checks.Ran := { declared := #[], outcomes := #[], finished := true }
  let mut printed : IO.Process.Output := { exitCode := 0, stdout := "", stderr := "" }
  for (modules, index) in (checkGroups lake).zipIdx do
    let (result?, output) ← runGroup lake loads dir index modules
    printed := { exitCode := max printed.exitCode output.exitCode, stdout := printed.stdout ++ output.stdout
                 stderr := printed.stderr ++ output.stderr }
    let some result := result? | return (none, printed)
    ran := { declared := ran.declared ++ result.declared, outcomes := ran.outcomes ++ result.outcomes
             finished := ran.finished && result.finished }
  return (some ran, printed)

def runOwnTest (lake : LakeFacts) (test : OwnTestFact) : IO OwnTestRun := do
  let args := match test.kind with
    | .script => #["script", "run", test.name]
    | .library => #["build", test.name]
    | .executable => #["exe", test.name]
  let code ← (← IO.Process.spawn { cmd := ← lakeCommand, args, cwd := lake.packageDir }).wait
  return { test, code }

def unrun (dir : System.FilePath) : String :=
  s!"{dir / "Checks.lean"}:1: the Checks runner did not start, as `lake lean` printed above, so no Check ran. Fix the \
    errors it reports in the package's modules, then run `lake test`."

def crashed (ran : Checks.Ran) (output : IO.Process.Output) : Checks.Ran :=
  let native := ((output.stdout ++ output.stderr).splitOn "\n").find?
    (·.contains "Could not find native implementation of external declaration")
  match native, ran.finished with
  | some line, false =>
    { ran with outcomes := ran.declared.map fun check => { check, elapsed := 0, error? := some line } }
  | _, _ => ran

def configFile (lake : LakeFacts) : String :=
  lake.configFiles[0]?.getD "lakefile.lean"

def configText (lake : LakeFacts) : IO String := do
  let some file := lake.configFiles[0]? | return ""
  return (← Read.readInput lake file .test).getD ""

def libraryPlace (lake : LakeFacts) (config : String) : Place :=
  { file := configFile lake, line := (((config.splitOn "\n").findIdx? (·.contains "lean_lib")).map (· + 1)).getD 1 }

def run (lakeFile nativeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .test
  let native ← Read.loadNative nativeFile
  let dir := lakeFile.parent.getD "."
  let (ran?, output) ← runChecks lake (native.loaded.map (s!"--load-dynlib={·.dynlib}")) dir
  unless ran?.any (·.finished) do
    IO.print output.stdout
    IO.eprint output.stderr
  let some ran := ran?.map (crashed · output) | do IO.eprintln (unrun dir); return 1
  let ownTests ← lake.ownTests.mapM (runOwnTest lake)
  let config ← configText lake
  let result := SoftwareChallenge.Test.run {
    declaredChecks := ran.declared
    checks := ran.outcomes
    declaredOwnTests := lake.ownTests
    ownTests
    unknownOwnTests := lake.testDriverArgs.filter fun name => !lake.ownTests.any (·.name == name)
    loadedObjects := native.objects config (configFile lake)
    linkedObjects := native.linked
    testDriverArgsPlace := lake.testDriverArgsPlace
    libraryPlace := libraryPlace lake config }
  let challengeFile := ((Read.challengeOf? lake).map (·.file)).getD "Challenge.lean"
  for line in Report.test challengeFile result do IO.println line
  return result.code

end SoftwareChallenge.Steps.Test

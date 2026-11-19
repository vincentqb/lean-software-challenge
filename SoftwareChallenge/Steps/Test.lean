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

def runnerSource (lake : LakeFacts) (out : System.FilePath) : String :=
  let listed := ", ".intercalate (lake.modules.map fun source =>
    s!"(`{source.module}, {(toJson source.file).compress})").toList
  "\n".intercalate (["import SoftwareChallenge.Steps.Checks"] ++ (lake.modules.map (s!"import {·.module}")).toList ++
    [s!"run_cmd SoftwareChallenge.Steps.Checks.run {(toJson out.toString).compress} #[{listed}]", ""])

def runChecks (lake : LakeFacts) (dir : System.FilePath) : IO (Option Checks.Ran × IO.Process.Output) := do
  let runner := dir / "Checks.lean"
  let out := dir / "checks.json"
  if ← out.pathExists then IO.FS.removeFile out
  IO.FS.writeFile runner (runnerSource lake out)
  let output ← IO.Process.output { cmd := ← lakeCommand, args := #["lean", runner.toString], cwd := lake.packageDir }
  unless ← out.pathExists do return (none, output)
  return ((Json.parse (← IO.FS.readFile out) >>= fromJson?).toOption, output)

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

def run (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .test
  let dir := lakeFile.parent.getD "."
  let (ran?, output) ← runChecks lake dir
  unless ran?.any (·.finished) do
    IO.print output.stdout
    IO.eprint output.stderr
  let some ran := ran?.map (crashed · output) | do IO.eprintln (unrun dir); return 1
  let ownTests ← lake.ownTests.mapM (runOwnTest lake)
  let result := SoftwareChallenge.Test.run {
    declaredChecks := ran.declared
    checks := ran.outcomes
    declaredOwnTests := lake.ownTests
    ownTests
    unknownOwnTests := lake.testDriverArgs.filter fun name => !lake.ownTests.any (·.name == name) }
  let challengeFile := ((Read.challengeOf? lake).map (·.file)).getD "Challenge.lean"
  for line in Report.test challengeFile result do IO.println line
  return result.code

end SoftwareChallenge.Steps.Test

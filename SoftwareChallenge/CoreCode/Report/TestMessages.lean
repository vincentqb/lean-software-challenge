module

public import SoftwareChallenge.CoreCode.Report.Message
public import SoftwareChallenge.CoreSpec.Test

public section

namespace SoftwareChallenge

open Lean

namespace Test

private def oneLine (text : String) : String :=
  " ".intercalate (((text.splitOn "\n").map (·.trimAscii.toString)).filter (!·.isEmpty))

private def lineOne (place : Place) : Place := { place with line := max 1 place.line }

private def kindName : OwnTestKind → String
  | .script => "script"
  | .library => "library"
  | .executable => "executable"

private def command (test : OwnTestFact) : String :=
  match test.kind with
  | .script => s!"lake script run {test.name}"
  | .library => s!"lake build {test.name}"
  | .executable => s!"lake exe {test.name}"

def nativeMissing? (error : String) : Option String :=
  match error.splitOn "Could not find native implementation of external declaration '" with
  | _ :: rest :: _ => (rest.splitOn "'").head?
  | _ => none

def Failure.message (challengeFile : String) : Failure → Message
  | .checkFailed outcome =>
    let check := outcome.check
    let place := lineOne check.place
    match nativeMissing? (outcome.error?.getD "") with
    | some declaration =>
      { place := ⟨"lakefile.lean", 1⟩
        what := s!"the Checks could not run: they call {declaration}, an `@[extern]` declaration, whose native code \
          Lean's interpreter finds only in precompiled modules"
        why := "and the package does not precompile them"
        fix := "Add `precompileModules := true` to the package's default lean_lib in lakefile.lean, then delete \
          owned.lock and run `lake build`"
        next := .test }
    | none =>
      { place, what := s!"the Check of {check.claim} failed: {oneLine (outcome.error?.getD "")}"
        why := s!"so either the Check is wrong or {check.claim} is false, since a Check tests a world claim against \
          the real foreign code"
        fix := s!"Fix the Check at {place.file}:{place.line}; if {check.claim} is false, no edit to the editable \
          files makes `lake test` pass, because the statement assumes it: the statement must drop {check.claim} from \
          the headlines of {challengeFile} and from its WorldSpec module, then delete owned.lock and run `lake build` \
          to record it"
        next := .test }
  | .checkNotRun check =>
    let place := lineOne check.place
    { place, what := s!"the Check of {check.claim} did not run"
      why := s!"so `lake test` cannot tell whether {check.claim} holds of the real foreign code"
      fix := s!"Make the Check at {place.file}:{place.line} return without ending the process, since a Check that \
        never returns or exits stops the Checks after it"
      next := .test }
  | .ownTest run =>
    let test := run.test
    let what := match test.kind with
      | .library => s!"library {test.name}, which testDriverArgs names, does not build"
      | kind => s!"{kindName kind} {test.name}, which testDriverArgs names, exited {run.code}"
    { place := lineOne test.place, what, why := "so the package's own tests fail"
      fix := s!"Run `{command test}` to see what it checks, and fix what it reports", next := .test }
  | .ownTestNotRun test =>
    { place := lineOne test.place, what := s!"{kindName test.kind} {test.name}, which testDriverArgs names, did not run"
      why := "so the package's own tests are not known to pass"
      fix := s!"Run `{command test}` to see why it does not start, and fix what it reports", next := .test }
  | .unknownOwnTest name place =>
    let place := lineOne place
    { place
      what := s!"testDriverArgs names {name}, but {place.file} declares no script, library, or executable {name}"
      why := "so it cannot run"
      fix := s!"Declare `script {name} do …` in {place.file}, or remove \"{name}\" from testDriverArgs; {place.file} \
        is owned, so then delete owned.lock and run `lake build`"
      next := .test }

end Test

end SoftwareChallenge

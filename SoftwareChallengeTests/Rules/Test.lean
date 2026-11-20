module

public meta import SoftwareChallenge.CoreCode.Rules.Test
public meta import SoftwareChallenge.CoreCode.Report.Report

public section

namespace SoftwareChallengeTests.Rules.Test

open Lean SoftwareChallenge

meta section

def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

def agrees : CheckFact :=
  { claim := `App.AddAgrees, statement := "AddAgrees nativeAdd", place := ⟨"App/WorldCode.lean", 12⟩ }

def advances : CheckFact :=
  { claim := `App.ClockAdvances, statement := "ClockAdvances 1", place := ⟨"App/WorldCode.lean", 30⟩ }

def passed (check : CheckFact) (elapsed : Nat) : CheckOutcome := { check, elapsed, error? := none }

def ownScript : OwnTestFact := { name := "own_test", kind := .script, place := ⟨"lakefile.lean", 40⟩ }

def ownLibrary : OwnTestFact := { name := "AppTests", kind := .library, place := ⟨"lakefile.lean", 20⟩ }

def ownExecutable : OwnTestFact := { name := "app_tests", kind := .executable, place := ⟨"lakefile.lean", 25⟩ }

def complete : TestFacts :=
  { declaredChecks := #[agrees, advances], checks := #[passed agrees 120, passed advances 1530],
    declaredOwnTests := #[ownScript, ownLibrary], ownTests := #[⟨ownScript, 0⟩, ⟨ownLibrary, 0⟩],
    unknownOwnTests := #[], testDriverArgsPlace := ⟨"lakefile.lean", 8⟩, libraryPlace := ⟨"lakefile.lean", 14⟩ }

#guard (Test.run complete).code == 0
#guard ((Test.run complete).timings.map (·.check.claim)) == #[`App.ClockAdvances, `App.AddAgrees]
#guard Report.test "Challenge.lean" (Test.run complete) ==
  #["App/WorldCode.lean:30 App.ClockAdvances  1.5 s", "App/WorldCode.lean:12 App.AddAgrees  0.1 s"]

def refuses (facts : TestFacts) (code : UInt32) (expected : Test.Failure → Bool) : Bool :=
  (Test.run facts).code == code && (Test.run facts).failures.any expected

def failing : TestFacts :=
  { complete with checks := #[{ passed agrees 120 with error? := some "expected 3,\n  got 4" }, passed advances 9] }

#guard refuses failing 1 (· matches .checkFailed { check := { claim := `App.AddAgrees, .. }, .. })

def notRun : TestFacts := { complete with checks := #[passed advances 9] }

#guard refuses notRun 1 (· matches .checkNotRun { claim := `App.AddAgrees, .. })

def movedCheck : TestFacts := { complete with checks := #[passed { agrees with place := ⟨"App/WorldCode.lean", 13⟩ } 1,
  passed advances 9] }

#guard refuses movedCheck 1 (· matches .checkNotRun { claim := `App.AddAgrees, .. })

def ownFails : TestFacts := { complete with ownTests := #[⟨ownScript, 2⟩, ⟨ownLibrary, 0⟩] }

#guard refuses ownFails 1 (· matches .ownTest { test := { name := "own_test", .. }, code := 2 })

def bothFail : TestFacts := { failing with ownTests := #[⟨ownScript, 2⟩, ⟨ownLibrary, 0⟩] }

#guard (Test.run bothFail).code == 1 && (Test.run bothFail).failures.size == 2

def ownNotRun : TestFacts := { complete with ownTests := #[⟨ownScript, 0⟩] }

#guard refuses ownNotRun 1 (· matches .ownTestNotRun { name := "AppTests", .. })

def unknown : TestFacts := { complete with unknownOwnTests := #["missing_test"] }

#guard refuses unknown 1 (· matches .unknownOwnTest "missing_test" ⟨"lakefile.lean", 8⟩)

def nativeError : String :=
  "Could not find native implementation of external declaration 'App.nativeAdd' (symbols 'l_App_nativeAdd___boxed' \
    or 'l_App_nativeAdd')"

def samples : Array Test.Failure :=
  #[.checkFailed { passed agrees 120 with error? := some "expected 3,\n  got 4" },
    .nativeCodeMissing { passed agrees 3 with error? := some nativeError } "App.nativeAdd" ⟨"lakefile.lean", 14⟩,
    .checkNotRun agrees, .ownTest ⟨ownScript, 2⟩, .ownTest ⟨ownLibrary, 1⟩, .ownTest ⟨ownExecutable, 3⟩,
    .ownTestNotRun ownLibrary, .unknownOwnTest "missing_test" ⟨"lakefile.lean", 8⟩]

def follows (message : Message) : Bool :=
  let text := (Report.item message).toLower
  !message.place.file.isEmpty && message.place.line ≥ 1 && !message.what.isEmpty && !message.why.isEmpty &&
    !message.fix.isEmpty && !contains text " ask " && !contains text "owner" && message.next == .test

#guard samples.all fun failure => follows (failure.message "Challenge.lean")

def says (failure : Test.Failure) (fragments : List String) : Bool :=
  fragments.all (contains (Report.item (failure.message "Challenge.lean")) ·)

#guard says (samples[0]!)
  ["App/WorldCode.lean:12: the Check of App.AddAgrees failed: expected 3, got 4, so either the Check is wrong or \
    App.AddAgrees is false", "Fix the Check at App/WorldCode.lean:12",
    "no edit to the editable files makes `lake test` pass", "headlines of Challenge.lean",
    "then run `lake test`."]
#guard !contains (Report.item ((samples[0]!).message "Challenge.lean")) "\n"
#guard says (.checkNotRun agrees) ["App/WorldCode.lean:12: the Check of App.AddAgrees did not run"]
#guard says (.ownTest ⟨ownScript, 2⟩)
  ["lakefile.lean:40: script own_test, which testDriverArgs names, exited 2, so the package's own tests fail",
    "Run `lake script run own_test` to see what it checks"]
#guard says (.ownTest ⟨ownLibrary, 1⟩)
  ["library AppTests, which testDriverArgs names, does not build", "Run `lake build AppTests`"]
#guard says (.ownTest ⟨ownExecutable, 3⟩) ["executable app_tests, which testDriverArgs names, exited 3", "`lake exe app_tests`"]
#guard says (.ownTestNotRun ownLibrary) ["library AppTests, which testDriverArgs names, did not run"]
#guard says (.unknownOwnTest "missing_test" ⟨"lakefile.lean", 8⟩)
  ["lakefile.lean:8: testDriverArgs names missing_test, but lakefile.lean declares no script, library, or executable \
    missing_test", "Declare `script missing_test do …` in lakefile.lean, or remove \"missing_test\" from \
    testDriverArgs", "delete owned.lock and run `lake build`"]

#guard (Report.test "Challenge.lean" (Test.run failing)).size == 3
#guard contains ((Report.test "Challenge.lean" (Test.run failing))[2]!) "the Check of App.AddAgrees failed"

def nativeMissing : TestFacts :=
  { complete with checks := #[{ passed agrees 3 with error? := some nativeError },
    { passed advances 4 with error? := some nativeError }] }

#guard Test.nativeMissing? nativeError == some "App.nativeAdd"
#guard Test.nativeMissing? "expected 3, got 4" == none
#guard refuses nativeMissing 1 (· matches .nativeCodeMissing _ "App.nativeAdd" ⟨"lakefile.lean", 14⟩)
#guard !(Test.run nativeMissing).failures.any (· matches .checkFailed _)
#guard says (samples[1]!)
  ["lakefile.lean:14: the Checks could not run: they call App.nativeAdd, an `@[extern]` declaration, whose native \
    code Lean's interpreter finds only in the libraries `lake test` loads, of precompiled modules and of \
    `extern_lib` targets, and none of them defines its symbol",
    "Declare in lakefile.lean an `extern_lib` whose static library holds the C function that App.nativeAdd's \
      `@[extern]` names and the `o.export` facet of its module, the object that defines its symbol, with \
      App.nativeAdd declared in a module that imports only Lean's own (Init, Std, Lean), since the Checks' process \
      runs that module's initializer, which calls its imports'; or add `precompileModules := true` to the lean_lib \
      of its module; then delete owned.lock and run `lake build`, then run `lake test`."]
#guard !says (samples[1]!) ["Fix the Check"]
#guard ((Report.test "Challenge.lean" (Test.run nativeMissing)).filter (contains · "extern_lib")).size == 1

end

end SoftwareChallengeTests.Rules.Test

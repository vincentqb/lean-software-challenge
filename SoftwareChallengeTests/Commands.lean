module

public import SoftwareChallengeTests.Fixtures.WorldCode
meta import SoftwareChallengeTests.Fixtures.WorldCode
meta import SoftwareChallengeTests.Fixtures.Sibling
meta import SoftwareChallengeTests.Fixtures.Rendezvous
meta import SoftwareChallengeTests.Support
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Commands

open SoftwareChallengeTests.Fixtures

rejects "doc comment" in WorldClaim Undocumented := True

Check SuccAgrees nativeSucc : nativeSucc 0 = 0 + 1
assert_evidence SuccAgrees = 4 checks

Check SuccAgrees nativeSucc := unless nativeSucc 1 == 2 do throw (IO.userError "nativeSucc 1 is not 2")
assert_evidence SuccAgrees = 5 checks

assert_evidence WrongSuccAgrees = 3 checks

rejects "`2 + 2 = 4` is not an instance of `SuccAgrees nativeSucc`, so" in Check SuccAgrees nativeSucc : 2 + 2 = 4
rejects "as in `Check SuccAgrees nativeSucc : nativeSucc ?n = ?n + 1`" in Check SuccAgrees nativeSucc : 2 + 2 = 4
rejects "give every argument" in Check SuccAgrees _ := pure ()
rejects "`SuccAgrees` is a WorldClaim that takes 1 more argument, `(succ : Nat → Nat)`" in Check SuccAgrees := pure ()
rejects "not a WorldClaim" in Check (2 = 2) : 2 = 2
rejects "not a WorldClaim" in Check (2 = 2) := pure ()
rejects "declaration failed" in Check SuccAgrees nativeSucc := (pure 0 : IO Nat)

rejects "marked as `meta`" in
  def runtimeEvidence : Bool := (SoftwareChallenge.allEvidence default).isEmpty

meta section

open Lean SoftwareChallenge

private def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

run_cmd Elab.Command.liftCoreM do
  let failures ← checkFailures #[(`SoftwareChallengeTests.Fixtures.WorldCode, "SoftwareChallengeTests/Fixtures/WorldCode.lean"),
    (`SoftwareChallengeTests.Fixtures.Sibling, "SoftwareChallengeTests/Fixtures/Sibling.lean")]
  unless failures.size == 3 && failures.all (contains · "of SoftwareChallengeTests.Fixtures.WrongSuccAgrees failed") &&
      failures.any (contains · "SoftwareChallengeTests/Fixtures/Sibling.lean:14:") &&
      failures.any (contains · "ran during the build") && failures.all (contains · "Then run `lake test`.") do
    throwError "The check runner misreported the fixture checks: {failures}"
  unless (← checkFailures #[]).isEmpty do throwError "The check runner ran checks of an unlisted module"

run_cmd Elab.Command.liftCoreM do
  let modules := #[(`SoftwareChallengeTests.Fixtures.Rendezvous, "SoftwareChallengeTests/Fixtures/Rendezvous.lean")]
  let dir ← Rendezvous.place
  let fresh : IO Unit := do if ← dir.pathExists then IO.FS.removeDirAll dir
  fresh
  let together ← runAllChecks modules (jobs := some 2)
  fresh
  let apart ← runAllChecks modules (jobs := some 1)
  fresh
  unless together.size == 2 && together.all (·.error.isNone) do
    throwError "Two Checks that meet did not run at the same time: {together.map (·.error)}"
  unless (apart.map (·.error.isSome)).toList == [true, false] do
    throwError "Two Checks run one after the other did not fail the first: {apart.map (·.error)}"
  let lines := timings #[{ file := "A.lean", line := 1, claim := `A, elapsed := 100, error := none },
    { file := "B.lean", line := 2, claim := `B, elapsed := 2500, error := none }]
  unless lines == #["B.lean:2 B  2.5 s", "A.lean:1 A  0.1 s"] do throwError "Check times were misreported: {lines}"

end

end SoftwareChallengeTests.Commands

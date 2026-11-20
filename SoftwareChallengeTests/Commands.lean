module

public import SoftwareChallengeTests.Fixtures.WorldCode
public import SoftwareChallengeTests.Fixtures.WitnessChallenge
meta import SoftwareChallengeTests.Fixtures.WorldCode
meta import SoftwareChallengeTests.Fixtures.Sibling
meta import SoftwareChallengeTests.Fixtures.Rendezvous
meta import SoftwareChallengeTests.Support
meta import SoftwareChallenge
meta import SoftwareChallenge.Steps.Checks

public section

namespace SoftwareChallengeTests.Commands

open SoftwareChallengeTests.Fixtures

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
rejects "declaration failed" in Check SuccAgrees nativeSucc := (pure 0 : IO Nat)

rejects "marked as `meta`" in
  def runtimeEvidence : Bool := SoftwareChallenge.isWorldClaim default .anonymous

#guard_expr type_of% WitnessChallenge.succ_vanishes_applies =ₐ
  ∃ f : Nat → Nat, ∃ n : Nat, SuccAgrees f ∧ f (WitnessChallenge.double n) = 0

theorem succ_vanishes_holds : type_of% WitnessChallenge.succ_vanishes :=
  fun _ agrees n vanishes => by have := agrees (WitnessChallenge.double n); omega

theorem succ_vanishes_applies_refuted : ¬ type_of% WitnessChallenge.succ_vanishes_applies :=
  fun ⟨_, n, agrees, vanishes⟩ => by have := agrees (WitnessChallenge.double n); omega

theorem double_listed_applies_holds : type_of% WitnessChallenge.double_listed_applies :=
  ⟨[], (fun _ listed => nomatch listed), rfl⟩

theorem succ_hits_one_everywhere_applies_holds : type_of% WitnessChallenge.succ_hits_one_everywhere_applies :=
  fun everywhere => ⟨0, everywhere 0⟩

#guard_expr type_of% WitnessChallenge.double_hidden_applies =ₐ
  ∃ n : Nat, ∃ n_1 : Nat, WitnessChallenge.double n < WitnessChallenge.double n + 1 ∧ 0 ≤ WitnessChallenge.double n_1

theorem double_hidden_applies_holds : type_of% WitnessChallenge.double_hidden_applies :=
  ⟨0, 0, Nat.lt_add_one _, Nat.zero_le _⟩

meta section

open Lean SoftwareChallenge

private def ranAt (out : System.FilePath) : IO SoftwareChallenge.Steps.Checks.Ran := do
  IO.ofExcept ((Lean.Json.parse (← IO.FS.readFile out)) >>= Lean.fromJson?)

private def runnerOut : IO System.FilePath := return (← IO.currentDir) / ".lake" / "check-runner-test.json"

private def rendezvousOutcomes (jobs : Nat) : Elab.Command.CommandElabM (Array Bool) := do
  let dir ← Rendezvous.place
  if ← dir.pathExists then IO.FS.removeDirAll dir
  let out ← runnerOut
  SoftwareChallenge.Steps.Checks.run out.toString
    #[(`SoftwareChallengeTests.Fixtures.Rendezvous, "SoftwareChallengeTests/Fixtures/Rendezvous.lean")] (jobs? := some jobs)
  if ← dir.pathExists then IO.FS.removeDirAll dir
  return (← ranAt out).outcomes.map (·.error?.isSome)

run_cmd do
  let out ← runnerOut
  SoftwareChallenge.Steps.Checks.run out.toString
    #[(`SoftwareChallengeTests.Fixtures.WorldCode, "SoftwareChallengeTests/Fixtures/WorldCode.lean"),
      (`SoftwareChallengeTests.Fixtures.Sibling, "SoftwareChallengeTests/Fixtures/Sibling.lean")]
  let failed := (← ranAt out).outcomes.filter (·.error?.isSome)
  unless failed.size == 3 && failed.all (·.check.claim == `SoftwareChallengeTests.Fixtures.WrongSuccAgrees) &&
      failed.any (·.check.place == ⟨"SoftwareChallengeTests/Fixtures/Sibling.lean", 14⟩) do
    throwError "The check runner misreported the fixture checks: {failed.map (·.check.place.line)}"
  SoftwareChallenge.Steps.Checks.run out.toString #[]
  unless (← ranAt out).outcomes.isEmpty do throwError "The check runner ran checks of an unlisted module"

run_cmd do
  let together ← rendezvousOutcomes 2
  let apart ← rendezvousOutcomes 1
  unless together == #[false, false] do throwError "Two Checks that meet did not run at the same time: {together}"
  unless apart == #[true, false] do throwError "Two Checks run one after the other did not fail the first: {apart}"

end

end SoftwareChallengeTests.Commands

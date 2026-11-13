module

public import SoftwareChallengeTests.Fixtures.WorldCode
meta import SoftwareChallengeTests.Fixtures.WorldCode
meta import SoftwareChallengeTests.Fixtures.Sibling
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

rejects "not an instance" in Check SuccAgrees nativeSucc : 2 + 2 = 4
rejects "give every argument" in Check SuccAgrees _ := pure ()
rejects "not a WorldClaim" in Check (2 = 2) : 2 = 2
rejects "not a WorldClaim" in Check (2 = 2) := pure ()
rejects "declaration failed" in Check SuccAgrees nativeSucc := (pure 0 : IO Nat)

rejects "marked as `meta`" in
  def runtimeEvidence : Bool := (SoftwareChallenge.allEvidence default).isEmpty

meta section

open Lean SoftwareChallenge

private def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

run_cmd Elab.Command.liftCoreM do
  let failures ← checkFailures #[`SoftwareChallengeTests.Fixtures.WorldCode, `SoftwareChallengeTests.Fixtures.Sibling]
  unless failures.size == 3 && failures.all (contains · "of SoftwareChallengeTests.Fixtures.WrongSuccAgrees failed") &&
      failures.any (contains · "Fixtures.Sibling, line 14") && failures.any (contains · "ran during the build") do
    throwError "The check runner misreported the fixture checks: {failures}"
  unless (← checkFailures #[]).isEmpty do throwError "The check runner ran checks of an unlisted module"

end

end SoftwareChallengeTests.Commands

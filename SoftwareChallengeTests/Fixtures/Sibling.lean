module

public import SoftwareChallengeTests.Fixtures.WorldSpec
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures

Check SuccAgrees nativeSucc : nativeSucc 1 = 1 + 1

Check SuccAgrees Nat.succ := pure ()

Check WrongSuccAgrees : wrongSucc 2 = 2 + 1

end SoftwareChallengeTests.Fixtures

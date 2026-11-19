module

public import SoftwareChallengeTests.Fixtures.WorldSpec
meta import SoftwareChallenge

set_option warn.sorry false

public section

namespace SoftwareChallengeTests.Fixtures.ClaimChallenge

def bump : Nat → Nat := sorry

theorem bump_grows (agrees : SuccAgrees nativeSucc) (n : Nat) : n < bump n := sorry

theorem bump_on_positives (agrees : ∀ m, m > 0 → SuccAt m) (n : Nat) : n ≤ bump n := sorry

theorem bump_at_leaves (agrees : SuccAt (leafSum 30 1)) (n : Nat) : bump n ≠ 0 := sorry

theorem bump_unchecked (agrees : Unchecked) (n : Nat) : bump n ≠ 1 := sorry

theorem bump_wrapped (agrees : SuccAgreesWrapped nativeSucc) (n : Nat) : bump n ≠ 2 := sorry

end SoftwareChallengeTests.Fixtures.ClaimChallenge

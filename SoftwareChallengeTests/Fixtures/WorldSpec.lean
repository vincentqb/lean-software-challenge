module

public import SoftwareChallengeTests.Fixtures.CoreSpec
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures

@[extern "lean_nat_succ"] opaque nativeSucc : @& Nat → Nat

@[extern "lean_nat_pred"] opaque wrongSucc : @& Nat → Nat

/-- The successor returns n + 1. Any other result falsifies it. -/
WorldClaim SuccAgrees (succ : Nat → Nat) := ∀ n, succ n = n + 1

/-- The wrong successor returns n + 1. It returns n - 1, so its checks fail. -/
WorldClaim WrongSuccAgrees := ∀ n, wrongSucc n = n + 1

/-- An assumption nothing checks. Any use of it falsifies the audit. -/
WorldClaim Unchecked := ∀ n, wrongSucc n = n

/-- The clock never runs backwards. A reading below an earlier one falsifies it. -/
WorldClaim ClockAdvances (now : Nat → Nat) := ∀ t, t ≤ now t

/-- The function returns its argument. Any other result falsifies it. -/
WorldClaim Identity (f : Nat → Nat) := ∀ n, f n = n

end SoftwareChallengeTests.Fixtures

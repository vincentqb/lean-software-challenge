module

public import SoftwareChallengeTests.Fixtures.CoreSpec
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures

@[extern "lean_nat_succ"] opaque nativeSucc : @& Nat → Nat

@[extern "lean_nat_pred"] opaque wrongSucc : @& Nat → Nat

WorldClaim SuccAgrees (succ : Nat → Nat) := ∀ n, succ n = n + 1

WorldClaim WrongSuccAgrees := ∀ n, wrongSucc n = n + 1

WorldClaim Unchecked := ∀ n, wrongSucc n = n

WorldClaim ClockAdvances (now : Nat → Nat) := ∀ t, t ≤ now t

WorldClaim SuccAt (n : Nat) := nativeSucc n = n + 1

WorldClaim UncheckedAt (n : Nat) := wrongSucc n = n

WorldClaim Identity (f : Nat → Nat) := ∀ n, f n = n

WorldClaim VanishesOnlyAtZero (f : Nat → Nat) := ∀ n, f n = 0 → n = 0

def SuccLaw : Prop := SuccAgrees nativeSucc → ∀ n, nativeSucc n = n + 1

@[expose] def SuccAgreesWrapped (succ : Nat → Nat) : Prop := SuccAgrees succ

WorldClaim SuccAgreesOn (listed : List Nat) := ∀ n ∈ listed, nativeSucc n = n + 1

end SoftwareChallengeTests.Fixtures

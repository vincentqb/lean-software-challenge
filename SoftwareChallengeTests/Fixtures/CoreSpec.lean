module

public section

namespace SoftwareChallengeTests.Fixtures

inductive Tree where
  | leaf
  | fork : Tree → Tree → Tree
  deriving Repr

def leafSum : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => leafSum n (2 * k) + leafSum n (2 * k + 1)

@[expose] def NegativeVanishes (f : Nat → Nat) : Prop := ∀ n, f n < 0 → f n = 0

def NonnegativeVanishes (f : Nat → Nat) : Prop := ∀ n, 0 ≤ f n → f n = 0

structure TwoLaws : Prop where
  first : 1 = 1
  second : 2 = 2

@[expose] def BothHold : Prop := 1 = 1 ∧ 2 = 2

end SoftwareChallengeTests.Fixtures

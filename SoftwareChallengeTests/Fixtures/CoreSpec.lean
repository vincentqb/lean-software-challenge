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

end SoftwareChallengeTests.Fixtures

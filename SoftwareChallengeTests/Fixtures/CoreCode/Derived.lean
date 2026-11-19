module

public section

namespace SoftwareChallengeTests.Fixtures

inductive Rose where
  | node (label : Nat) (children : List Rose)
  deriving Repr, BEq

noncomputable def lostHole (n : Nat) : Nat := n

end SoftwareChallengeTests.Fixtures

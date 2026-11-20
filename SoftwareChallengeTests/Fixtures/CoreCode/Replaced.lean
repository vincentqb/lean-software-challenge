module

public section

namespace SoftwareChallengeTests.Fixtures.CoreCode.Replaced

inductive Coin where
  | heads
  | tails (n : Nat)

def tailsAfter (n : Nat) : Coin := Coin.tails (n + 1)

attribute [implemented_by tailsAfter] Coin.tails

end SoftwareChallengeTests.Fixtures.CoreCode.Replaced

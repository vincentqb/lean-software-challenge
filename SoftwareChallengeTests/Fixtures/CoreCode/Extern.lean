module

public section

namespace SoftwareChallengeTests.Fixtures.CoreCode.Extern

inductive Coin where
  | heads
  | tails (n : Nat)

attribute [extern "lean_nat_succ"] Coin.tails

end SoftwareChallengeTests.Fixtures.CoreCode.Extern

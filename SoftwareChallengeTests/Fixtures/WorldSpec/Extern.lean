module

public section

namespace SoftwareChallengeTests.Fixtures.WorldSpec.Extern

inductive Coin where
  | heads
  | tails (n : Nat)

attribute [extern "lean_nat_succ"] Coin.tails

@[extern "lean_nat_succ"] def Width : Type := Nat

end SoftwareChallengeTests.Fixtures.WorldSpec.Extern

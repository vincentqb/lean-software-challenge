module

public section

namespace SoftwareChallengeTests.Fixtures.CoreCode.Replaced

inductive Coin where
  | heads
  | tails (n : Nat)

def tailsAfter (n : Nat) : Coin := Coin.tails (n + 1)

attribute [implemented_by tailsAfter] Coin.tails

def coinRec.{u} {motive : Coin → Sort u} (heads : motive Coin.heads) (tails : (n : Nat) → motive (Coin.tails n))
    (coin : Coin) : motive coin :=
  Coin.casesOn coin heads tails

attribute [implemented_by coinRec] Coin.rec

end SoftwareChallengeTests.Fixtures.CoreCode.Replaced

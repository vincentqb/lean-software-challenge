module

public section

namespace SoftwareChallengeTests.Fixtures.CoreCode.Generated

inductive Rose where
  | node (label : Nat) (children : List Rose)
  deriving Repr, BEq, Ord, Hashable

inductive Term where
  | lit (value : Nat)
  | add (left right : Term)
  deriving Repr, BEq, Ord, DecidableEq

structure Point where
  x : Nat
  y : Nat
  deriving Repr, BEq, DecidableEq

inductive Cached where
  | leaf (value : Nat)
  | pair (left right : Cached)
with
  @[computed_field] total : Cached → Nat
    | .leaf value => value
    | .pair left right => left.total + right.total

def size : Term → Nat
  | .lit _ => 1
  | .add left right => size left + size right + 1

def halve (n : Nat) : Nat := if n < 2 then 0 else halve (n - 2) + 1
termination_by n
decreasing_by omega

def countdown (n : Nat) : Option Nat := if n = 0 then some 0 else countdown (n - 1)
partial_fixpoint

theorem size_pos (term : Term) : 0 < size term := by
  cases term <;> simp [size]

def index (term : Term) : Nat := term.ctorIdx

end SoftwareChallengeTests.Fixtures.CoreCode.Generated

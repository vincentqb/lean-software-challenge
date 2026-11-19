module

meta import SoftwareChallenge.CoreCode.Match

namespace SoftwareChallengeTests.Match

open Lean SoftwareChallenge

meta def replaceable : Name → Bool := (· == `hole)

meta def hole : Shape := .const `hole []

meta def constant (value : Nat) : Shape := .lam (.const ``Nat []) (.natLit value)

meta def equation (left right : Shape) : Shape :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Nat [])) left) right

meta def statement (function : Shape) : Shape := equation (.app function (.natLit 0)) (.app function (.natLit 0))

meta def other (function : Shape) : Shape := equation (.app function (.natLit 1)) (.natLit 1)

#guard (statement hole).isKill replaceable (statement (constant 1)).negation

#guard !(statement hole).isKill replaceable (.app (.const ``Decidable []) (statement (constant 1)))

#guard !(statement hole).isKill replaceable (statement (.bvar 0)).negation

#guard !(statement hole).isKill replaceable
  (equation (.app (constant 1) (.natLit 0)) (.app (constant 2) (.natLit 0))).negation

#guard !(statement hole).isKill replaceable
  (equation (.app (constant 1) (.natLit 1)) (.app (constant 1) (.natLit 0))).negation

#guard (statement hole).independent replaceable [other hole]
  (Shape.conjunction [(statement (constant 1)).negation, other (constant 1)])

#guard !(statement hole).independent replaceable [] (statement (constant 1)).negation

#guard !(statement hole).independent replaceable [other hole]
  (Shape.conjunction [(statement (constant 1)).negation, other (constant 2)])

#guard !(statement hole).independent (fun name => replaceable name || name == ``And) [other hole]
  (Shape.conjunction [(statement (constant 1)).negation, other (constant 1)])

end SoftwareChallengeTests.Match

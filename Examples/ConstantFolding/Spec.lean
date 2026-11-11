module

public import Examples.ConstantFolding.Boundary
meta import Examples.ConstantFolding.Boundary
public meta import SoftwareChallenge

public section

namespace Examples.ConstantFolding

inductive Expr where
  | lit (value : Nat)
  | var (index : Nat)
  | add (left right : Expr)

@[expose] def eval (env : Nat → Nat) : Expr → Nat
  | .lit n => n
  | .var x => env x
  | .add a b => eval env a + eval env b

@[expose] def Expr.isLit : Expr → Bool
  | .lit _ => true
  | _ => false

@[expose] def normal : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .add a b => normal a && normal b && !(a.isLit && b.isLit)

@[expose] def closed : Expr → Bool
  | .lit _ => true
  | .var _ => false
  | .add a b => closed a && closed b

/-- The adder agrees with `Nat.add`. A different sum for any pair falsifies it. -/
WorldClaim AddAgrees (add : Nat → Nat → Nat) := ∀ a b, add a b = a + b

Check AddAgrees nativeAdd : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71

Conjecture Normalizes (optimize : Expr → Expr) := ∀ e, normal (optimize e) = true

end Examples.ConstantFolding

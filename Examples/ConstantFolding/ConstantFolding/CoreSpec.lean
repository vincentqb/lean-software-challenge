module

public section

namespace ConstantFolding

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

end ConstantFolding

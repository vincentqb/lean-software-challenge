module

public import SoftwareChallenge.CoreSpec.Shape
public import Lean.Expr

public section

namespace SoftwareChallenge

open Lean

def Universe.ofLevel : Level → Universe
  | .zero => .zero
  | .succ level => .succ (ofLevel level)
  | .max left right => .max (ofLevel left) (ofLevel right)
  | .imax left right => .imax (ofLevel left) (ofLevel right)
  | .param name => .param name
  | .mvar id => .mvar id.name

theorem Universe.ofLevel_injective : Function.Injective Universe.ofLevel := by
  intro left
  induction left <;> intro right equal <;> cases right <;>
    simp only [Universe.ofLevel, reduceCtorEq, Universe.succ.injEq, Universe.max.injEq, Universe.imax.injEq,
      Universe.param.injEq, Universe.mvar.injEq] at equal
  case zero.zero => rfl
  case succ.succ injective _ => rw [injective equal]
  case max.max leftInjective rightInjective _ _ | imax.imax leftInjective rightInjective _ _ =>
    rw [leftInjective equal.1, rightInjective equal.2]
  case param.param => rw [equal]
  case mvar.mvar left right => cases left; cases right; cases equal; rfl

@[expose] def Shape.ofExpr : Expr → Shape
  | .bvar index => .bvar index
  | .fvar id => .fvar id.name
  | .mvar id => .mvar id.name
  | .sort level => .sort (Universe.ofLevel level)
  | .const name levels => .const name (levels.map Universe.ofLevel)
  | .app function argument => .app (ofExpr function) (ofExpr argument)
  | .lam _ type body _ => .lam (ofExpr type) (ofExpr body)
  | .forallE _ type body _ => .forallE (ofExpr type) (ofExpr body)
  | .letE _ type value body _ => .letE (ofExpr type) (ofExpr value) (ofExpr body)
  | .lit (.natVal value) => .natLit value
  | .lit (.strVal value) => .strLit value
  | .mdata _ expr => ofExpr expr
  | .proj structureName index value => .proj structureName index (ofExpr value)

end SoftwareChallenge

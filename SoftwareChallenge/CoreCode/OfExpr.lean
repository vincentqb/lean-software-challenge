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

theorem Shape.ofExpr_mdata (data : MData) (expr : Expr) : Shape.ofExpr (.mdata data expr) = Shape.ofExpr expr := rfl

end SoftwareChallenge

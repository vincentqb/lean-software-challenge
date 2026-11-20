import Lean.Expr

namespace SoftwareChallenge

open Lean

inductive Shape where
  | bvar (index : Nat)
  | fvar (name : Name)
  | mvar (name : Name)
  | sort (level : Level)
  | const (name : Name) (levels : List Level)
  | app (function argument : Shape)
  | lam (type body : Shape)
  | forallE (type body : Shape)
  | letE (type value body : Shape)
  | natLit (value : Nat)
  | strLit (value : String)
  | proj (structureName : Name) (index : Nat) (value : Shape)
  deriving BEq

namespace Shape

def ofExpr : Expr → Shape
  | .bvar index => .bvar index
  | .fvar id => .fvar id.name
  | .mvar id => .mvar id.name
  | .sort level => .sort level.normalize
  | .const name levels => .const name (levels.map (·.normalize))
  | .app function argument => .app (ofExpr function) (ofExpr argument)
  | .lam _ type body _ => .lam (ofExpr type) (ofExpr body)
  | .forallE _ type body _ => .forallE (ofExpr type) (ofExpr body)
  | .letE _ type value body _ => .letE (ofExpr type) (ofExpr value) (ofExpr body)
  | .lit (.natVal value) => .natLit value
  | .lit (.strVal value) => .strLit value
  | .mdata _ expr => ofExpr expr
  | .proj structureName index value => .proj structureName index (ofExpr value)

def closedUnder (depth : Nat) : Shape → Bool
  | .bvar index => index < depth
  | .app function argument => function.closedUnder depth && argument.closedUnder depth
  | .lam type body | .forallE type body => type.closedUnder depth && body.closedUnder (depth + 1)
  | .letE type value body => type.closedUnder depth && value.closedUnder depth && body.closedUnder (depth + 1)
  | .proj _ _ value => value.closedUnder depth
  | _ => true

def subst (σ : List (Name × Shape)) : Shape → Shape
  | .const name levels => ((σ.find? (·.1 == name)).map (·.2)).getD (.const name levels)
  | .app function argument => .app (function.subst σ) (argument.subst σ)
  | .lam type body => .lam (type.subst σ) (body.subst σ)
  | .forallE type body => .forallE (type.subst σ) (body.subst σ)
  | .letE type value body => .letE (type.subst σ) (value.subst σ) (body.subst σ)
  | .proj structureName index value => .proj structureName index (value.subst σ)
  | shape => shape

def collect (holes : Name → Bool) : Shape → Shape → List (Name × Shape) → List (Name × Shape)
  | .const name levels, target, σ =>
    if holes name && !σ.any (·.1 == name) && target != .const name levels then (name, target) :: σ else σ
  | .app f a, .app g b, σ => collect holes a b (collect holes f g σ)
  | .lam t b, .lam u c, σ | .forallE t b, .forallE u c, σ => collect holes b c (collect holes t u σ)
  | .letE t v b, .letE u w c, σ => collect holes b c (collect holes v w (collect holes t u σ))
  | .proj _ _ v, .proj _ _ w, σ => collect holes v w σ
  | _, _, σ => σ

def rejects (holes : Name → Bool) (headline kill : Shape) : Bool :=
  match kill with
  | .app (.const ``Not []) rejected =>
    let σ := collect holes headline rejected []
    !σ.isEmpty && σ.all (·.2.closedUnder 0) && headline.subst σ == rejected
  | _ => false

end Shape

end SoftwareChallenge

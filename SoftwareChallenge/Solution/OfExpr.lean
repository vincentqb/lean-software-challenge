module

public import SoftwareChallenge.CoreCode.OfExpr
public import SoftwareChallenge.CoreSpec.Expr

public section

namespace SoftwareChallenge

open Lean

theorem ExprSimilar.ofExpr_eq {left right : Expr} (similar : ExprSimilar left right) :
    Shape.ofExpr left = Shape.ofExpr right := by
  induction similar <;> simp_all [Shape.ofExpr]

private theorem ExprSimilar.of_unwrapped {left right : Expr}
    (unwrapped : ∀ right, (∀ data inner, right ≠ .mdata data inner) →
      Shape.ofExpr left = Shape.ofExpr right → ExprSimilar left right)
    (equal : Shape.ofExpr left = Shape.ofExpr right) : ExprSimilar left right := by
  induction right with
  | mdata _ _ inner => exact .mdataRight (inner equal)
  | _ => exact unwrapped _ (fun _ _ => nofun) equal

theorem ExprSimilar.of_ofExpr_eq {left right : Expr} (equal : Shape.ofExpr left = Shape.ofExpr right) :
    ExprSimilar left right := by
  induction left generalizing right
  case mdata inner => exact .mdataLeft (inner equal)
  case' lit literal => cases literal
  all_goals
    refine ExprSimilar.of_unwrapped ?_ equal
    clear equal right
    intro right unwrapped equal
    cases right
    case mdata => exact absurd rfl (unwrapped _ _)
    case lit literal =>
      cases literal <;> simp only [Shape.ofExpr, reduceCtorEq, Shape.natLit.injEq, Shape.strLit.injEq] at equal <;>
        exact equal ▸ .refl _
    all_goals simp only [Shape.ofExpr, reduceCtorEq, Shape.bvar.injEq, Shape.fvar.injEq, Shape.mvar.injEq,
      Shape.sort.injEq, Shape.const.injEq, Shape.app.injEq, Shape.lam.injEq, Shape.forallE.injEq,
      Shape.letE.injEq, Shape.proj.injEq] at equal
  case bvar.bvar => exact equal ▸ .refl _
  case fvar.fvar left right | mvar.mvar left right => cases left; cases right; cases equal; exact .refl _
  case sort.sort => exact Universe.ofLevel_injective equal ▸ .refl _
  case const.const =>
    obtain ⟨rfl, levels⟩ := equal
    exact (List.map_inj_right fun _ _ => (Universe.ofLevel_injective ·)).1 levels ▸ .refl _
  case app.app functionSimilar argumentSimilar _ _ => exact .app (functionSimilar equal.1) (argumentSimilar equal.2)
  case lam.lam typeSimilar bodySimilar _ _ _ _ => exact .lam (typeSimilar equal.1) (bodySimilar equal.2)
  case forallE.forallE typeSimilar bodySimilar _ _ _ _ => exact .forallE (typeSimilar equal.1) (bodySimilar equal.2)
  case letE.letE typeSimilar valueSimilar bodySimilar _ _ _ _ _ =>
    exact .letE (typeSimilar equal.1) (valueSimilar equal.2.1) (bodySimilar equal.2.2)
  case proj.proj valueSimilar _ _ _ =>
    obtain ⟨rfl, rfl, equal⟩ := equal
    exact .proj (valueSimilar equal)

theorem Shape.ofExpr_eq_iff (left right : Expr) : Shape.ofExpr left = Shape.ofExpr right ↔ ExprSimilar left right :=
  ⟨ExprSimilar.of_ofExpr_eq, ExprSimilar.ofExpr_eq⟩

theorem Shape.ofExpr_eq_iff_rejects_constant :
    ¬ ∀ (left right : Expr),
      (fun (_ : Expr) => Shape.natLit 0) left = (fun (_ : Expr) => Shape.natLit 0) right ↔ ExprSimilar left right := by
  intro constant
  nomatch (constant (.bvar 0) (.bvar 1)).1 rfl

end SoftwareChallenge

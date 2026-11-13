module

public import ConstantFolding.CoreSpec

public section

namespace ConstantFolding

private def combine : Expr → Expr → Expr
  | .lit a, .lit b => .lit (a + b)
  | a, b => .add a b

def fold : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .add a b => combine (fold a) (fold b)

private theorem eval_combine (env : Nat → Nat) (a b : Expr) :
    eval env (combine a b) = eval env a + eval env b := by
  cases a <;> cases b <;> rfl

theorem eval_fold (env : Nat → Nat) (e : Expr) :
    eval env (fold e) = eval env e := by
  induction e <;> simp_all [fold, eval, eval_combine]

theorem fold_eq_lit_of_closed (e : Expr) (h : closed e = true) : ∃ n, fold e = .lit n := by
  induction e with
  | lit n => exact ⟨n, rfl⟩
  | var x => simp [closed] at h
  | add a b ha hb =>
    simp only [closed, Bool.and_eq_true] at h
    obtain ⟨n, hn⟩ := ha h.1
    obtain ⟨m, hm⟩ := hb h.2
    exact ⟨n + m, by simp [fold, hn, hm, combine]⟩

theorem fold_eq_self_of_normal (e : Expr) (h : normal e = true) : fold e = e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb =>
    simp only [normal, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨na, nb⟩, mixed⟩ := h
    simp only [fold, ha na, hb nb]
    cases a <;> cases b <;> simp_all [combine, Expr.isLit]

theorem normal_fold (e : Expr) : normal (fold e) = true := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb =>
    simp only [fold]
    generalize fold a = x at ha
    generalize fold b = y at hb
    cases x <;> cases y <;> simp_all [combine, normal, Expr.isLit]

end ConstantFolding

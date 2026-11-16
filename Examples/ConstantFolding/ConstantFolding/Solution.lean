module

public import ConstantFolding.WorldCode
meta import SoftwareChallenge

public section

namespace ConstantFolding

theorem fold_preserves_meaning (env : Nat → Nat) (e : Expr) :
    eval env (fold e) = eval env e :=
  eval_fold env e

theorem fold_closed_literal (e : Expr) (h : closed e = true) : ∃ n, fold e = .lit n :=
  fold_eq_lit_of_closed e h

theorem fold_normalizes (e : Expr) : normal (fold e) = true :=
  normal_fold e

theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=
  fold_eq_self_of_normal (fold e) (normal_fold e)

theorem fold_keeps_literal (n m : Nat) (h : fold (.lit n) = .lit m) : m = n := by
  rw [fold_eq_self_of_normal (Expr.lit n) rfl] at h
  injection h with h
  exact h.symm

theorem fold_keeps_literal_rejects_zero :
    ¬ ∀ (n m : Nat), (fun (_ : Expr) => Expr.lit 0) (.lit n) = .lit m → m = n := by
  intro h
  exact absurd (h 1 0 rfl) (by decide)

theorem fold_keeps_literal_applies : ∃ (n m : Nat), fold (.lit n) = .lit m :=
  ⟨0, 0, fold_eq_self_of_normal _ rfl⟩

theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :
    output e = toString (eval (fun _ => 0) e) := by
  simp only [output, evalNative_eq agrees, fold_preserves_meaning]

theorem fold_preserves_meaning_rejects_constant :
    ¬ ∀ (env : Nat → Nat) (e : Expr), eval env ((fun _ => Expr.lit 0) e) = eval env e := by
  intro h
  exact absurd (h (fun _ => 0) (.lit 1)) (by decide)

theorem fold_closed_literal_rejects_identity :
    ¬ ∀ (e : Expr), closed e = true → ∃ n, id e = .lit n := by
  intro h
  obtain ⟨n, hn⟩ := h (.add (.lit 1) (.lit 2)) rfl
  cases hn

theorem fold_normalizes_rejects_identity : ¬ ∀ e, normal (id e) = true := by
  intro h
  exact absurd (h (.add (.lit 1) (.lit 2))) (by decide)

theorem fold_idempotent_rejects_increment :
    ¬ ∀ e : Expr, (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e => Expr.lit (eval (fun _ => 0) e + 1)) e) =
      (fun e => Expr.lit (eval (fun _ => 0) e + 1)) e := by
  intro h
  have := h (.lit 0)
  simp [eval] at this

theorem output_correct_rejects_suffix :
    ¬ (AddAgrees Nat.add → ∀ e : Expr,
      (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e)) := by
  intro h
  have := congrArg String.length (h (fun _ _ => rfl) (.lit 0))
  simp at this

end ConstantFolding

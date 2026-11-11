module

public import ConstantFolding.Shell

public section

namespace ConstantFolding

theorem fold_preserves_meaning (env : Nat → Nat) (e : Expr) :
    eval env (fold e) = eval env e :=
  eval_fold env e

theorem fold_closed_literal (e : Expr) (h : closed e = true) : ∃ n, fold e = .lit n :=
  fold_eq_lit_of_closed e h

theorem fold_idempotent (normalizes : Normalizes fold) (e : Expr) : fold (fold e) = fold e :=
  fold_eq_self_of_normal (fold e) (normalizes e)

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

theorem fold_idempotent_rejects_increment :
    ¬ (Normalizes (fun e => Expr.lit (eval (fun _ => 0) e + 1)) → ∀ e : Expr,
      (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e => Expr.lit (eval (fun _ => 0) e + 1)) e) =
        (fun e => Expr.lit (eval (fun _ => 0) e + 1)) e) := by
  intro h
  have := h (fun _ => rfl) (.lit 0)
  simp [eval] at this

theorem output_correct_rejects_suffix :
    ¬ (AddAgrees Nat.add → ∀ e : Expr,
      (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e)) := by
  intro h
  have := congrArg String.length (h (fun _ _ => rfl) (.lit 0))
  simp at this

end ConstantFolding

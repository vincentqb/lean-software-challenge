module

public import ConstantFolding.Output

public section

namespace ConstantFolding

theorem addAgrees_consistent :
    ∃ (nativeAdd : Nat → Nat → Nat), ∀ (a b : Nat), nativeAdd a b = a + b :=
  ⟨fun a b => a + b, fun _ _ => rfl⟩

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

theorem output_correct (e : Expr) : output e = toString (eval (fun _ => 0) e) := by
  simp only [output, evalNative_eq, fold_preserves_meaning]

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

theorem fold_keeps_literal_rejects_zero :
    ¬ ∀ (n m : Nat), (fun (_ : Expr) => Expr.lit 0) (.lit n) = .lit m → m = n := by
  intro h
  exact absurd (h 1 0 rfl) (by decide)

theorem output_correct_rejects_suffix :
    ¬ ∀ e : Expr, (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e) := by
  intro h
  have := congrArg String.length (h (.lit 0))
  simp at this

theorem fold_preserves_meaning_applies : ∃ (_ : Nat → Nat) (_ : Expr), True := ⟨fun _ => 0, .lit 0, trivial⟩

theorem fold_closed_literal_applies : ∃ (e : Expr) (_ : closed e = true) (_ : Nat), True :=
  ⟨.lit 0, rfl, 0, trivial⟩

theorem fold_normalizes_applies : ∃ (_ : Expr), True := ⟨.lit 0, trivial⟩

theorem fold_idempotent_applies : ∃ (_ : Expr), True := ⟨.lit 0, trivial⟩

theorem fold_keeps_literal_applies : ∃ (n m : Nat) (_ : fold (.lit n) = .lit m), True :=
  ⟨0, 0, fold_eq_self_of_normal _ rfl, trivial⟩

theorem output_correct_applies : ∃ (_ : Expr), True := ⟨.lit 0, trivial⟩

end ConstantFolding

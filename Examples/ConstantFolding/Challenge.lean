module

public import ConstantFolding.CoreSpec
public import ConstantFolding.WorldSpec
meta import SoftwareChallenge

public section

/-!
# Constant folding

Folding preserves meaning, leaves no constant subexpression, removes every constant
subexpression of a closed expression, and is idempotent, and the output is the true value.
Not claimed: anything about the native adder beyond `AddAgrees nativeAdd`.
-/

namespace ConstantFolding

def fold : Expr → Expr := sorry

def output (e : Expr) : String := sorry

theorem fold_preserves_meaning (env : Nat → Nat) (e : Expr) :
    eval env (fold e) = eval env e := by
  sorry

theorem fold_closed_literal (e : Expr) (h : closed e = true) : ∃ n, fold e = .lit n := by
  sorry

theorem fold_normalizes (e : Expr) : normal (fold e) = true := by
  sorry

theorem fold_idempotent (e : Expr) : fold (fold e) = fold e := by
  sorry

theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :
    output e = toString (eval (fun _ => 0) e) := by
  sorry

@[kills fold_preserves_meaning] theorem fold_preserves_meaning_rejects_constant :
    ¬ ∀ (env : Nat → Nat) (e : Expr), eval env ((fun _ => Expr.lit 0) e) = eval env e := by
  sorry

@[kills fold_closed_literal] theorem fold_closed_literal_rejects_identity :
    ¬ ∀ (e : Expr), closed e = true → ∃ n, id e = .lit n := by
  sorry

@[kills fold_normalizes] theorem fold_normalizes_rejects_identity : ¬ ∀ e, normal (id e) = true := by
  sorry

@[kills fold_idempotent] theorem fold_idempotent_rejects_increment :
    ¬ ∀ e : Expr, (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e => Expr.lit (eval (fun _ => 0) e + 1)) e) =
      (fun e => Expr.lit (eval (fun _ => 0) e + 1)) e := by
  sorry

@[kills output_correct] theorem output_correct_rejects_suffix :
    ¬ (AddAgrees Nat.add → ∀ e : Expr,
      (fun e => toString (eval (fun _ => 0) e) ++ "!") e = toString (eval (fun _ => 0) e)) := by
  sorry

end ConstantFolding

import SoftwareChallenge.Problem
import SoftwareChallengeTests.Harness

namespace SoftwareChallengeTests

open SoftwareChallenge

structure Fixture where
  rule : Rule
  edits : List Edit := []
  candidate : List Edit := []
  command : Array String
  code : UInt32
  says : List String

def challenge : String := "Challenge.lean"

def solution : String := "ConstantFolding/Solution.lean"

def statement : Array String := #["build", "statement"]

def lint : Array String := #["lint"]

def countdown : List Edit := [
  .replace challenge "end ConstantFolding" "def countdown (n : Nat) : Option Nat := sorry

theorem countdown_returns (n : Nat) : countdown n = some 0 := by
  sorry

@[kills countdown_returns] theorem countdown_returns_rejects_none :
    ¬ ∀ (n : Nat), (fun (_ : Nat) => (none : Option Nat)) n = some 0 := by
  sorry

end ConstantFolding",
  .write "ConstantFolding/Countdown.lean" "module

public section

namespace ConstantFolding

def countdown (n : Nat) : Option Nat := if n = 0 then some 0 else countdown (n - 1)
partial_fixpoint

theorem countdown_eq (n : Nat) : countdown n = some 0 := by
  induction n with
  | zero => rw [countdown]; simp
  | succ k ih => rw [countdown]; simpa using ih

end ConstantFolding
",
  .replace solution "public import ConstantFolding.Output" "public import ConstantFolding.Output
public import ConstantFolding.Countdown",
  .replace solution "end ConstantFolding" "theorem countdown_returns (n : Nat) : countdown n = some 0 := countdown_eq n

theorem countdown_returns_rejects_none :
    ¬ ∀ (n : Nat), (fun (_ : Nat) => (none : Option Nat)) n = some 0 := by
  intro h
  cases h 0

theorem countdown_returns_applies : ∃ (_ : Nat), True := ⟨0, trivial⟩

end ConstantFolding",
  .write "ConstantFolding/Main.lean" "module

import ConstantFolding.Output
import ConstantFolding.Countdown

public section

def main : IO Unit := do
  IO.println (ConstantFolding.output (.add (.lit 2) (.lit 3)))
  IO.println (ConstantFolding.countdown 3)
"]

def fixtures : List Fixture := [
  { rule := .kill, command := statement, code := 1, says := ["headline ConstantFolding.fold_normalizes has no kill"]
    edits := [.replace challenge "@[kills fold_normalizes] theorem fold_normalizes_rejects_identity : \
      ¬ ∀ e, normal (id e) = true := by\n  sorry\n\n" ""] },
  { rule := .killShape, command := statement, code := 1
    says := ["kill ConstantFolding.fold_keeps_literal_rejects_zero does not negate headline",
      "kill ConstantFolding.fold_normalizes_rejects_identity does not negate headline",
      "kill ConstantFolding.fold_idempotent_rejects_increment does not negate headline"]
    edits := [.replace challenge "(fun (_ : Expr) => Expr.lit 0) (.lit n) = .lit m → m = n := by"
        "fold (.lit n) = .lit m → m = n := by",
      .replace challenge "¬ ∀ e, normal (id e) = true" "¬ ∀ e, normal ((fun _ => e) e) = true",
      .replace challenge "(fun e => Expr.lit (eval (fun _ => 0) e + 1)) e) =\n      (fun e => Expr.lit (eval (fun _ => 0) e + 1)) e"
        "(fun e => Expr.lit (eval (fun _ => 0) e + 1)) e) = e"] },
  { rule := .witness, command := statement, code := 1
    says := ["has no witness ConstantFolding.fold_normalizes_applies",
      "has no witness ConstantFolding.fold_folds_closed_applies stating \
        `∃ (e : ConstantFolding.Expr), ∃ (a : ConstantFolding.closed e = true), True`",
      "headline ConstantFolding.fold_folds_closed concludes with ConstantFolding.Literal, whose body the witness \
        cannot see", "Mark ConstantFolding.Literal `@[expose]` in ConstantFolding/Expr.lean:31",
      "has no witness ConstantFolding.fold_never_literal_applies stating `∃ (n : Nat), True`",
      "has no witness ConstantFolding.fold_keeps_closed_fixes_normal_applies stating \
        `(∃ (e : ConstantFolding.Expr), ∃ (a : ConstantFolding.closed e = true), True) ∧ \
        ∃ (e : ConstantFolding.Expr), ∃ (a : ConstantFolding.normal e = true), True`",
      "has no witness ConstantFolding.fold_fixes_some_literal_applies stating \
        `∃ (n : Nat), ∃ (e : ConstantFolding.Expr), ∃ (a : e = ConstantFolding.Expr.lit n), True`",
      "has no witness ConstantFolding.fold_all_closed_applies stating \
        `∃ (e : ConstantFolding.Expr), ∃ (h : ConstantFolding.closed e = true), True`"]
    edits := [.replace challenge "@[kills fold_normalizes]"
        "theorem fold_normalizes_applies : True := by\n  sorry\n\n@[kills fold_normalizes]",
      .replace "ConstantFolding/Expr.lean" "end ConstantFolding" "def Literal (e : Expr) : Prop := ∃ n, e = .lit n\n\n\
        @[expose] def FoldsClosed (f : Expr → Expr) : Prop := ∀ e, closed e = true → Literal (f e)\n\n\
        @[expose] def NeverLiteral (e : Expr) : Prop := ∀ n, e = .lit n → False\n\n\
        @[expose] def KeepsClosedFixesNormal (f : Expr → Expr) : Prop :=\n  \
        (∀ e, closed e = true → closed (f e) = true) ∧ ∀ e, normal e = true → f e = e\n\n\
        @[expose] def FixesSomeLiteral (f : Expr → Expr) : Prop := ∃ n, ∀ e, e = .lit n → f e = e\n\n\
        @[expose] def AllClosed : Expr → Prop\n  | .lit _ => True\n  | .var _ => False\n  \
        | .add a b => AllClosed a ∧ AllClosed b\n\nend ConstantFolding",
      .replace challenge "end ConstantFolding" "theorem fold_folds_closed : FoldsClosed fold := by\n  sorry\n\n\
        theorem fold_folds_closed_applies : True := by\n  sorry\n\n\
        @[kills fold_folds_closed] theorem fold_folds_closed_rejects_identity : ¬ FoldsClosed id := by\n  sorry\n\n\
        theorem fold_never_literal : NeverLiteral (fold (.var 0)) := by\n  sorry\n\n\
        theorem fold_never_literal_applies : True := by\n  sorry\n\n\
        @[kills fold_never_literal] theorem fold_never_literal_rejects_constant :\n    \
        ¬ NeverLiteral ((fun (_ : Expr) => Expr.lit 0) (.var 0)) := by\n  sorry\n\n\
        theorem fold_keeps_closed_fixes_normal : KeepsClosedFixesNormal fold := by\n  sorry\n\n\
        theorem fold_keeps_closed_fixes_normal_applies : True := by\n  sorry\n\n\
        @[kills fold_keeps_closed_fixes_normal] theorem fold_keeps_closed_fixes_normal_rejects_variable :\n    \
        ¬ KeepsClosedFixesNormal (fun _ => Expr.var 0) := by\n  sorry\n\n\
        theorem fold_fixes_some_literal : FixesSomeLiteral fold := by\n  sorry\n\n\
        theorem fold_fixes_some_literal_applies : True := by\n  sorry\n\n\
        @[kills fold_fixes_some_literal] theorem fold_fixes_some_literal_rejects_doubling :\n    \
        ¬ FixesSomeLiteral (fun e => Expr.add e e) := by\n  sorry\n\n\
        theorem fold_all_closed (e : Expr) (h : closed e = true) : AllClosed (fold e) := by\n  sorry\n\n\
        theorem fold_all_closed_applies : True := by\n  sorry\n\n\
        @[kills fold_all_closed] theorem fold_all_closed_rejects_variable :\n    \
        ¬ ∀ (e : Expr), closed e = true → AllClosed ((fun _ => Expr.var 0) e) := by\n  sorry\n\n\
        end ConstantFolding"] },
  { rule := .consistent, command := statement, code := 1, says := ["no @[consistent] theorem states"]
    edits := [.replace challenge "∀ (a b : Nat), nativeAdd a b = a + b := by" "∀ (a b : Nat), nativeAdd a b = b + a := by"] },
  { rule := .terminates, command := statement, code := 1
    says := ["@[terminates ConstantFolding.output] marks ConstantFolding.fold_keeps_literal"]
    edits := [.replace challenge "theorem fold_keeps_literal (n m : Nat)"
      "@[terminates output] theorem fold_keeps_literal (n m : Nat)"] },
  { rule := .pending, command := lint, code := 2
    says := ["headline ConstantFolding.fold_idempotent uses sorry", "Proved: 5 of 6 headlines",
      "hole ConstantFolding.simplify is not implemented yet", "hole ConstantFolding.evaluate is not implemented yet"]
    edits := [.replace solution "fold (fold e) = fold e :=\n  fold_eq_self_of_normal (fold e) (normal_fold e)"
        "fold (fold e) = fold e := by\n  sorry",
      .replace challenge "def output (e : Expr) : String := sorry" "def output (e : Expr) : String := sorry\n\n\
        def simplify (e : Expr) : Expr := sorry\n\ndef evaluate (e : Expr) : Nat := sorry",
      .replace "ConstantFolding/Fold.lean" "end ConstantFolding" "def evaluate (e : Expr) : Nat := sorry\n\nend ConstantFolding"] },
  { rule := .axiomUsed, command := lint, code := 1
    says := ["headline ConstantFolding.fold_idempotent uses the axiom ConstantFolding.fold_idempotent_fact",
      "consistency theorem ConstantFolding.addAgrees_consistent uses the axiom ConstantFolding.addAgrees"]
    edits := [.replace solution "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
      fold_eq_self_of_normal (fold e) (normal_fold e)" "axiom fold_idempotent_fact (e : Expr) : fold (fold e) = fold e\n\n\
      theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  fold_idempotent_fact e",
      .replace solution "⟨fun a b => a + b, fun _ _ => rfl⟩" "⟨nativeAdd, addAgrees⟩"] },
  { rule := .impure, command := lint, code := 1
    says := ["ConstantFolding.render, which hole ConstantFolding.output computes through, is @[implemented_by]",
      "ConstantFolding.renderNat, which hole ConstantFolding.output computes through, is unsafe"]
    edits := [.replace "ConstantFolding/Output.lean" "@[expose] def output (e : Expr) : String := toString"
      "def renderNat (n : Nat) : String := unsafe (unsafeCast (toString n))\n\n@[expose, implemented_by renderNat] \
        def render (n : Nat) : String := toString n\n\n@[expose] def output (e : Expr) : String := render",
      .replace solution "simp only [output, evalNative_eq" "simp only [output, render, evalNative_eq"] },
  { rule := .fixpoint, command := lint, code := 1, edits := countdown
    says := ["hole ConstantFolding.countdown is a partial_fixpoint without a @[terminates ConstantFolding.countdown]"] },
  { rule := .unreached, command := lint, code := 1, says := ["does not reach hole ConstantFolding.fold"]
    edits := [.replace "ConstantFolding/Main.lean" "IO.println (ConstantFolding.output (.add (.lit 2) (.lit 3)))"
      "IO.println \"5\""] },
  { rule := .untested, command := lint, code := 1
    says := ["world claim ConstantFolding.addAgrees has no test that `lake test` runs"]
    edits := [.replace "ConstantFolding/Tests.lean" "def main := SoftwareChallenge.testsMain" "def main : IO UInt32 := pure 0"] },
  { rule := .owned, command := #["exe", "grade", "candidate"], code := 1
    says := ["changes the owned files ConstantFolding/Expr.lean"]
    candidate := [.replace "ConstantFolding/Expr.lean" "end ConstantFolding"
      "theorem eval_lit (env : Nat → Nat) (n : Nat) : eval env (.lit n) = n := rfl\n\nend ConstantFolding"] }]

def coverage : List Edit := countdown ++ [
  .replace challenge "theorem countdown_returns (n" "@[terminates countdown] theorem countdown_returns (n",
  .replace "lakefile.lean" "root := `ConstantFolding.Main" "root := `Main",
  .replace "lakefile.lean" "testDriver := \"tests\"" "testDriver := \"constant_folding/tests\"",
  .write "Main.lean" "module

import ConstantFolding.Output
import ConstantFolding.Countdown

public section

def main : IO Unit := do
  IO.println (ConstantFolding.output (.add (.lit 2) (.lit 3)))
  IO.println (ConstantFolding.countdown 3)
",
  .replace "lakefile.lean" "lean_lib «Challenge» where" "lean_lib «Helpers» where\n  roots := #[`Helpers]\n\n\
    lean_lib «Challenge» where",
  .write "Helpers.lean" "module

public section

namespace Helpers

inductive Tree where
  | leaf
  | node (children : List Tree)
  deriving Repr, BEq

structure Box where
  value : Nat
  deriving Repr, DecidableEq, Hashable

instance : Inhabited Box := ⟨⟨0⟩⟩

abbrev Count := Nat

def structural : Nat → Count
  | 0 => 0
  | n + 1 => structural n

def wellFounded (n : Nat) : Nat := if h : n ≤ 1 then n else wellFounded (n / 2)
termination_by n
decreasing_by omega

def withWhere (n : Nat) : Nat := go n
where go (m : Nat) : Nat := m

def matching : Nat → Bool
  | 0 => true
  | _ => false

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

class Sized (α : Type) where
  size : α → Nat

instance : Sized Box := ⟨Box.value⟩

def withLetRec (n : Nat) : Nat :=
  let rec go : Nat → Nat
    | 0 => 0
    | k + 1 => go k
  go n

partial def looping (n : Nat) : Nat := if n > 100 then n else looping (n * 2 + 1)

unsafe def unsafely (n : Nat) : Nat := n

@[implemented_by unsafely] def viaUnsafe (n : Nat) : Nat := n

@[extern \"lean_nat_add\"] opaque external : @& Nat → @& Nat → Nat

def everything (n : Nat) : Nat :=
  structural n + wellFounded n + withWhere n + (if matching n then 1 else 0) + looping n + viaUnsafe n +
    external n n + (default : Box).value + (if Tree.leaf == Tree.node [] then 1 else 0) + (hash (Box.mk n)).toNat +
    (if decide (Box.mk n = Box.mk 0) then 1 else 0) + (toString (repr Tree.leaf ++ repr (Box.mk n))).length +
    (if isEven n then 1 else 0) + Sized.size (Box.mk n) + withLetRec n

end Helpers
",
  .replace "ConstantFolding/Fold.lean" "public import ConstantFolding.Expr" "public import ConstantFolding.Expr\npublic import Helpers",
  .replace "ConstantFolding/Fold.lean" "  | .lit n => .lit n\n  | .var x => .var x\n  | .add a b => combine"
    "  | .lit n => let _ := Helpers.everything n; .lit n\n  | .var x => .var x\n  | .add a b => combine",
  .replace challenge "@[kills fold_preserves_meaning]" "theorem fold_agrees (f : Expr → Expr)
    (h : ∀ e, eval (fun _ => 0) (f e) = eval (fun _ => 0) e) (e : Expr) :
    eval (fun _ => 0) (f (fold e)) = eval (fun _ => 0) e := by
  sorry

@[kills fold_agrees] theorem fold_agrees_rejects_constant :
    ¬ ∀ (f : Expr → Expr), (∀ e, eval (fun _ => 0) (f e) = eval (fun _ => 0) e) → ∀ (e : Expr),
      eval (fun _ => 0) (f ((fun _ => Expr.lit 1) e)) = eval (fun _ => 0) e := by
  sorry

theorem fold_folds_closed : FoldsClosed fold := by
  sorry

@[kills fold_folds_closed] theorem fold_folds_closed_rejects_identity : ¬ FoldsClosed id := by
  sorry

@[kills fold_preserves_meaning]",
  .replace "ConstantFolding/Expr.lean" "end ConstantFolding"
    "@[expose] def FoldsClosed (f : Expr → Expr) : Prop := ∀ e, closed e = true → ∃ n, f e = .lit n\n\nend ConstantFolding",
  .replace solution "end ConstantFolding" "theorem fold_agrees (f : Expr → Expr)
    (h : ∀ e, eval (fun _ => 0) (f e) = eval (fun _ => 0) e) (e : Expr) :
    eval (fun _ => 0) (f (fold e)) = eval (fun _ => 0) e := by
  rw [h, fold_preserves_meaning]

theorem fold_agrees_rejects_constant :
    ¬ ∀ (f : Expr → Expr), (∀ e, eval (fun _ => 0) (f e) = eval (fun _ => 0) e) → ∀ (e : Expr),
      eval (fun _ => 0) (f ((fun _ => Expr.lit 1) e)) = eval (fun _ => 0) e := by
  intro h
  exact absurd (h id (fun _ => rfl) (.lit 0)) (by decide)

theorem fold_agrees_applies :
    ∃ (f : Expr → Expr) (_ : ∀ e, eval (fun _ => 0) (f e) = eval (fun _ => 0) e) (_ : Expr), True :=
  ⟨id, fun _ => rfl, .lit 0, trivial⟩

theorem fold_folds_closed : FoldsClosed fold := fold_eq_lit_of_closed

theorem fold_folds_closed_rejects_identity : ¬ FoldsClosed id := by
  intro h
  obtain ⟨n, hn⟩ := h (.add (.lit 1) (.lit 2)) rfl
  cases hn

theorem fold_folds_closed_applies : ∃ (e : Expr) (_ : closed e = true) (_ : Nat), True :=
  ⟨.lit 0, rfl, 0, trivial⟩

end ConstantFolding"]

def coverageSays : List String := [
  "Errors: 4", "Helpers.looping, which hole ConstantFolding.fold computes through, is partial",
  "Helpers.viaUnsafe, which hole ConstantFolding.fold computes through, is @[implemented_by]",
  "Helpers.unsafely, which hole ConstantFolding.fold computes through, is unsafe",
  "Helpers.external, which hole ConstantFolding.fold computes through, is @[extern]",
  "Proved: 9 of 9 headlines, 9 of 9 kills, 9 of 9 witnesses, 1 of 1 consistency theorems"]

end SoftwareChallengeTests

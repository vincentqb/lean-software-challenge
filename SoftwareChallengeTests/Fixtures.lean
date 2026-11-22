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
    says := ["headline ConstantFolding.fold_keeps_literal has no witness",
      "Add `@[witness ConstantFolding.fold_keeps_literal] theorem fold_keeps_literal_applies : ∃ (n : Nat), \
        ∃ (m : Nat), ConstantFolding.fold (ConstantFolding.Expr.lit n) = ConstantFolding.Expr.lit m := by sorry`",
      "@[witness ConstantFolding.fold_keeps_literal_rejects_zero] marks ConstantFolding.fold_keeps_literal_applies, \
        but ConstantFolding.fold_keeps_literal_rejects_zero is not a headline"]
    edits := [.replace challenge "@[witness fold_keeps_literal]" "@[witness fold_keeps_literal_rejects_zero]"] },
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

@[kills fold_preserves_meaning]",
  .replace solution "end ConstantFolding" "theorem fold_agrees (f : Expr → Expr)
    (h : ∀ e, eval (fun _ => 0) (f e) = eval (fun _ => 0) e) (e : Expr) :
    eval (fun _ => 0) (f (fold e)) = eval (fun _ => 0) e := by
  rw [h, fold_preserves_meaning]

theorem fold_agrees_rejects_constant :
    ¬ ∀ (f : Expr → Expr), (∀ e, eval (fun _ => 0) (f e) = eval (fun _ => 0) e) → ∀ (e : Expr),
      eval (fun _ => 0) (f ((fun _ => Expr.lit 1) e)) = eval (fun _ => 0) e := by
  intro h
  exact absurd (h id (fun _ => rfl) (.lit 0)) (by decide)

end ConstantFolding"]

def coverageSays : List String := [
  "Errors: 4", "Helpers.looping, which hole ConstantFolding.fold computes through, is partial",
  "Helpers.viaUnsafe, which hole ConstantFolding.fold computes through, is @[implemented_by]",
  "Helpers.unsafely, which hole ConstantFolding.fold computes through, is unsafe",
  "Helpers.external, which hole ConstantFolding.fold computes through, is @[extern]",
  "Proved: 8 of 8 headlines, 8 of 8 kills, 1 of 1 witnesses, 1 of 1 consistency theorems"]

end SoftwareChallengeTests

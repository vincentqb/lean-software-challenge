module

public section

namespace SoftwareChallengeTests.Fixtures.Statements

theorem zero_right (n : Nat) : n + 0 = n := rfl

theorem zero_right_renamed (m : Nat) : m + 0 = m := rfl

theorem zero_right_implicit {n : Nat} : n + 0 = n := rfl

theorem zero_right_strict ⦃n : Nat⦄ : n + 0 = n := rfl

theorem zero_right_marked (n : Nat) : (no_index n) + 0 = n := rfl

theorem zero_right_assuming (n : Nat) (_ : n = n) : n + 0 = n := rfl

theorem zero_right_flipped (n : Nat) : n = n + 0 := rfl

theorem add_swap (a b : Nat) : a + b = b + a := Nat.add_comm a b

theorem add_swap_reordered (b a : Nat) : a + b = b + a := Nat.add_comm a b

@[expose] def twice (n : Nat) : Nat := n + n

theorem twice_eq (n : Nat) : twice n = n + n := rfl

theorem twice_eq_unfolded (n : Nat) : n + n = n + n := rfl

theorem twice_twice (n : Nat) : twice (twice n) = twice (twice n) := rfl

theorem twice_twice_composed (n : Nat) : (twice ∘ twice) n = twice (twice n) := rfl

theorem in_u.{u} (α : Sort u) (a : α) : a = a := rfl

theorem in_v.{v} (α : Sort v) (a : α) : a = a := rfl

theorem in_one (α : Sort 1) (a : α) : a = a := rfl

theorem in_uv.{u, v} (α : Sort u) (β : Sort v) (a : α) (b : β) : a = a ∧ b = b := ⟨rfl, rfl⟩

theorem in_vu.{v, u} (α : Sort u) (β : Sort v) (a : α) (b : β) : a = a ∧ b = b := ⟨rfl, rfl⟩

set_option linter.defProp false in
def zero_right_def (n : Nat) : n + 0 = n := rfl

def hole (n : Nat) : Nat := n

abbrev hole_abbrev (n : Nat) : Nat := n

opaque hole_opaque : Nat → Nat

partial def hole_partial (n : Nat) : Nat := hole_partial n

unsafe def hole_unsafe (n : Nat) : Nat := n

def hole_optional (n : Nat := 0) : Nat := n

def aux_one : Nat := 1

def aux_two : Nat := 2

end SoftwareChallengeTests.Fixtures.Statements

module

public import SoftwareChallengeTests.Fixtures.CoreSpec
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures

def halve (n : Nat) : Nat :=
  if h : n < 2 then 0 else halve (n - 2) + 1
termination_by n
decreasing_by omega

private def helper (n : Nat) : Nat := n

def identity (n : Nat) : Nat := helper n

theorem bounded (n : Nat) (h : n < 5) : n < 6 := by omega

theorem identity_fixed (n : Nat) : identity n = n := by simp [identity, helper]

theorem identity_fixed_again (m : Nat) : identity m = m := identity_fixed m

theorem identity_fixed_rejects_successor : ¬ ∀ n : Nat, (fun n => n + 1) n = n := by
  intro h
  exact absurd (h 0) (by decide)

theorem identity_fixed_rejects_bound : ¬ ∀ n : Nat, (fun _ => n + 1) n = n := by
  intro h
  exact absurd (h 0) (by decide)

theorem mismatched_negation : ¬ ∀ n : Nat, n = n + 1 := by
  intro h
  exact absurd (h 0) (by decide)

theorem identity_three : identity 3 = 3 := by simp [identity, helper]

theorem identity_three_rejects_successor : ¬ (fun n : Nat => n + 1) 3 = 3 := by decide

theorem identity_twice (n : Nat) : identity (identity n) = identity n := by simp [identity, helper]

theorem identity_twice_rejects_successor :
    ¬ ∀ n : Nat, (fun n => n + 1) ((fun n => n + 1) n) = (fun n => n + 1) n := by
  intro h
  exact absurd (h 0) (by decide)

theorem identity_fixed_rejects_independently :
    (¬ ∀ n : Nat, (fun _ => 0) n = n) ∧ ∀ n : Nat, (fun _ => 0) ((fun _ => 0) n) = (fun _ => 0) n :=
  ⟨fun h => absurd (h 1) (by decide), fun _ => rfl⟩

theorem identity_fixed_rejects_independently_mixed :
    (¬ ∀ n : Nat, (fun _ => 0) n = n) ∧ ∀ n : Nat, id (id n) = id n :=
  ⟨fun h => absurd (h 1) (by decide), fun _ => rfl⟩

theorem identity_twice_rejects_mixed : ¬ ∀ n : Nat, (fun n => n + 1) (id n) = id n := by
  intro h
  exact absurd (h 0) (by decide)

theorem identity_twice_rejects_marked :
    ¬ ∀ n : Nat, (no_index (fun n => n + 1)) ((fun n => n + 1) n) = (fun n => n + 1) n := by
  intro h
  exact absurd (h 0) (by decide)

theorem identity_succ (n : Nat) : identity (Nat.succ n) = Nat.succ n := by simp [identity, helper]

theorem identity_succ_rejects_successor :
    ¬ ∀ n : Nat, (fun n => n + 1) ((no_index Nat.succ) n) = Nat.succ n := by
  intro h
  exact absurd (h 0) (by decide)

theorem uses_unnamed (h : 1 = 2) : 1 = 2 := h

def pick (_ : Nat) : Nat := 0

theorem pick_one_zero (n : Nat) (h : pick n = 1) : n = 0 := by simp [pick] at h

theorem pick_one_zero_has_no_witness : ¬ ∃ n, pick n = 1 := by simp [pick]

inductive Rose where
  | node (label : Nat) (children : List Rose)
  deriving Repr, BEq

noncomputable def lostHole (n : Nat) : Nat := n

/-- A claim outside a WorldSpec module. Declaring it here falsifies the audit. -/
WorldClaim CoreClaim := 1 = 1

end SoftwareChallengeTests.Fixtures

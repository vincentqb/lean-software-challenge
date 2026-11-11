module

public section

namespace SoftwareChallengeTests.Fixtures.Fixpoint

def countdown (n : Nat) : Option Nat := if n = 0 then some 0 else countdown (n - 1)
partial_fixpoint

def spin (n : Nat) : Option Nat := if n = 0 then some 0 else spin (n - 1)
partial_fixpoint

theorem countdown_terminates (n : Nat) : (countdown n).isSome := by
  induction n with
  | zero => rw [countdown]; rfl
  | succ n ih => rw [countdown]; simpa using ih

theorem countdown_terminates_rejects_stuck :
    ¬ ∀ n : Nat, ((fun _ : Nat => (none : Option Nat)) n).isSome := by
  intro h
  exact absurd (h 0) (by decide)

theorem countdown_zero : countdown 0 = some 0 := by rw [countdown]; rfl

theorem countdown_zero_rejects_one : ¬ (fun _ : Nat => some 1) 0 = some 0 := by decide

end SoftwareChallengeTests.Fixtures.Fixpoint

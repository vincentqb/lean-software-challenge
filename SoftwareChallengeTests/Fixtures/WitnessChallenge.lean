module

public import SoftwareChallengeTests.Fixtures.WorldSpec
meta import SoftwareChallenge

set_option warn.sorry false

public section

namespace SoftwareChallengeTests.Fixtures.WitnessChallenge

def double : Nat → Nat := sorry

theorem double_halves (n : Nat) (h : double n = 4) : n = 2 := sorry

theorem double_positive (unused n : Nat) (h : 0 < double n) : 0 < n := sorry

@[witness double_positive] theorem double_positive_applies : ∃ n, 0 < double n := sorry

@[witness double_positive] theorem double_positive_applies_unused : ∃ unused n : Nat, 0 < double n := sorry

@[witness double_positive] theorem double_positive_applies_replaced : ∃ n, 0 < (fun n => 2 * n) n := sorry

theorem double_between (m n : Nat) (low : double m < double n) (high : double n < 10) : m < n := sorry

@[witness double_between] theorem double_between_applies : ∃ m n, double m < double n ∧ double n < 10 := sorry

theorem double_lengths (α : Type) (xs : List α) (h : xs.length = double 1) : xs ≠ [] := sorry

@[witness double_lengths] theorem double_lengths_applies :
    ∃ (α : Type) (xs : List α), xs.length = double 1 := sorry

theorem succ_hits_one (agrees : SuccAgrees nativeSucc) (n : Nat) (h : nativeSucc n = 1) : n = 0 := sorry

@[witness succ_hits_one] theorem succ_hits_one_applies : SuccAgrees nativeSucc → ∃ n, nativeSucc n = 1 := sorry

theorem double_small (n : Nat) (h : n < 3) : double n < 6 := sorry

theorem double_zero : double 0 = 0 := sorry

@[witness double_zero] theorem double_zero_applies : True := sorry

theorem double_negative_vanishes : NegativeVanishes double := sorry

theorem double_nonnegative_vanishes : NonnegativeVanishes double := sorry

@[witness double_nonnegative_vanishes] theorem double_nonnegative_vanishes_applies : ∃ n, 0 ≤ double n := sorry

theorem double_vanishes_only_at_zero : VanishesOnlyAtZero double := sorry

theorem double_zero_fin (n : Nat) [NeZero n] (h : double (0 : Fin n).val = 0) : 0 < n := sorry

@[witness double_zero_fin] theorem double_zero_fin_applies :
    ∃ (n : Nat) (_ : NeZero n), double (0 : Fin n).val = 0 := sorry

theorem succ_law : SuccLaw := sorry

@[witness double] theorem double_applies : ∃ n : Nat, 0 < n := sorry

end SoftwareChallengeTests.Fixtures.WitnessChallenge

module

public import SoftwareChallengeTests.Fixtures.WorldSpec
meta import SoftwareChallenge

set_option warn.sorry false

public section

namespace SoftwareChallengeTests.Fixtures.WitnessChallenge

def double : Nat → Nat := sorry

theorem double_halves (n : Nat) (h : double n = 4) : n = 2 := sorry

@[kills double_halves] theorem double_halves_rejects_shift :
    ¬ ∀ n : Nat, (fun n => 2 * n + 2) n = 4 → n = 2 := sorry

theorem double_positive (unused n : Nat) (h : 0 < double n) : 0 < n := sorry

@[kills double_positive] theorem double_positive_rejects_one :
    ¬ ∀ (unused n : Nat), 0 < (fun _ => 1) n → 0 < n := sorry

@[kills double_positive] theorem double_positive_rejects_two :
    ¬ ∀ (unused n : Nat), 0 < (fun _ => 2) n → 0 < n := sorry

theorem double_between (m n : Nat) (low : double m < double n) (high : double n < 10) : m < n := sorry

@[kills double_between] theorem double_between_rejects_reversal :
    ¬ ∀ (m n : Nat), (fun k => 10 - k) m < (fun k => 10 - k) n → (fun k => 10 - k) n < 10 → m < n := sorry

theorem double_lengths (α : Type) (xs : List α) (h : xs.length = double 1) : xs ≠ [] := sorry

@[kills double_lengths] theorem double_lengths_rejects_zero :
    ¬ ∀ (α : Type) (xs : List α), xs.length = (fun _ => 0) 1 → xs ≠ [] := sorry

theorem succ_hits_one (agrees : SuccAgrees nativeSucc) (n : Nat) (h : nativeSucc n = 1) : n = 0 := sorry

@[kills succ_hits_one] theorem succ_hits_one_rejects_identity :
    ¬ (SuccAgrees (fun n => n) → ∀ n : Nat, (fun n => n) n = 1 → n = 0) := sorry

theorem double_small (n : Nat) (h : n < 3) : double n < 6 := sorry

@[kills double_small] theorem double_small_rejects_ten : ¬ ∀ n : Nat, n < 3 → (fun _ => 10) n < 6 := sorry

theorem double_zero : double 0 = 0 := sorry

@[kills double_zero] theorem double_zero_rejects_one : ¬ (fun _ => 1) 0 = 0 := sorry

theorem double_negative_vanishes : NegativeVanishes double := sorry

@[kills double_negative_vanishes] theorem double_negative_vanishes_rejects_one :
    ¬ NegativeVanishes (fun _ => 1) := sorry

theorem double_nonnegative_vanishes : NonnegativeVanishes double := sorry

@[kills double_nonnegative_vanishes] theorem double_nonnegative_vanishes_rejects_one :
    ¬ NonnegativeVanishes (fun _ => 1) := sorry

theorem double_vanishes_only_at_zero : VanishesOnlyAtZero double := sorry

@[kills double_vanishes_only_at_zero] theorem double_vanishes_only_at_zero_rejects_zero :
    ¬ VanishesOnlyAtZero (fun _ => 0) := sorry

theorem double_zero_fin (n : Nat) [NeZero n] (h : double (0 : Fin n).val = 0) : 0 < n := sorry

@[kills double_zero_fin] theorem double_zero_fin_rejects_one :
    ¬ ∀ (n : Nat) [NeZero n], (fun _ => 1) (0 : Fin n).val = 0 → 0 < n := sorry

theorem double_first (n : Nat) (h : 0 < double n) (first : (⟨0, h⟩ : Fin (double n)).val = 0) : 0 < n := sorry

@[kills double_first] theorem double_first_rejects_one :
    ¬ ∀ (n : Nat) (h : 0 < (fun _ => 1) n), (⟨0, h⟩ : Fin ((fun _ => 1) n)).val = 0 → 0 < n := sorry

theorem double_fin (i : Fin (double 2)) : i.val < 4 := sorry

@[kills double_fin] theorem double_fin_rejects_five : ¬ ∀ i : Fin ((fun _ => 5) 2), i.val < 4 := sorry

theorem double_under_claim (n : Nat) (_h : ∀ m, m > 0 → SuccAt m) (small : double n < 5) : n < 6 := sorry

@[kills double_under_claim] theorem double_under_claim_rejects_zero :
    ¬ ∀ (n : Nat), (∀ m, m > 0 → SuccAt m) → (fun _ => 0) n < 5 → n < 6 := sorry

theorem double_at (n : Nat) (_c : SuccAt n) (h : double n = 1) : n = 0 := sorry

@[kills double_at] theorem double_at_rejects_one : ¬ ∀ (n : Nat), SuccAt n → (fun _ => 1) n = 1 → n = 0 := sorry

theorem double_assumes_wrapped (agrees : SuccAgreesWrapped nativeSucc) (n : Nat) :
    double (nativeSucc n) = 2 * n + 2 := sorry

@[kills double_assumes_wrapped] theorem double_assumes_wrapped_rejects_zero :
    ¬ (SuccAgreesWrapped (fun n => n + 1) → ∀ n : Nat, (fun _ => 0) ((fun n => n + 1) n) = 2 * n + 2) := sorry

theorem double_hidden (n : Nat) (h : double n < double n + 1) : NonnegativeVanishes double := sorry

@[kills double_hidden] theorem double_hidden_rejects_four :
    ¬ ∀ n : Nat, (fun _ => 4) n < (fun _ => 4) n + 1 → NonnegativeVanishes (fun _ => 4) := sorry

theorem double_odd (n : Nat) (h : double n = 3) : False := sorry

theorem double_odd_applies : ∃ n, double n = 3 := sorry

@[kills double_odd] theorem double_odd_rejects_three : ¬ ∀ n : Nat, (fun _ => 3) n = 3 → False := sorry

@[kills double] theorem double_rejects_nothing : ¬ ∀ n : Nat, n = n := sorry

theorem succ_law : SuccLaw := sorry

theorem succ_vanishes (f : Nat → Nat) (agrees : SuccAgrees f) (n : Nat) (vanishes : f (double n) = 0) : False :=
  sorry

@[kills succ_vanishes] theorem succ_vanishes_rejects_zero :
    ¬ ∀ (f : Nat → Nat), SuccAgrees f → ∀ n : Nat, f ((fun _ => 0) n) = 0 → False := sorry

theorem double_listed (listed : List Nat) (agrees : SuccAgreesOn listed) (h : (listed.map double).sum = 0) :
    listed.sum = 0 := sorry

@[kills double_listed] theorem double_listed_rejects_zero :
    ¬ ∀ (listed : List Nat), SuccAgreesOn listed → (listed.map (fun _ => 0)).sum = 0 → listed.sum = 0 := sorry

theorem succ_hits_one_at (n : Nat) (h : SuccAt n) (k : nativeSucc n = 1) : n = 0 := sorry

@[kills succ_hits_one_at] theorem succ_hits_one_at_rejects_identity :
    ¬ ∀ (n : Nat), SuccAt n → (fun n => n) n = 1 → n = 0 := sorry

theorem succ_hits_one_everywhere (h : ∀ m, SuccAt m) (n : Nat) (k : nativeSucc n = 1) : n = 0 := sorry

@[kills succ_hits_one_everywhere] theorem succ_hits_one_everywhere_rejects_identity :
    ¬ ((∀ m, SuccAt m) → ∀ n : Nat, (fun n => n) n = 1 → n = 0) := sorry

end SoftwareChallengeTests.Fixtures.WitnessChallenge

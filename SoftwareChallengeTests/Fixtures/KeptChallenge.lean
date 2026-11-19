module

meta import SoftwareChallenge

set_option warn.sorry false

public section

namespace SoftwareChallengeTests.Fixtures.KeptChallenge

def double : Nat → Nat := sorry

theorem double_positive_one (_h : 0 < double 1) : double 1 ≠ 0 := sorry

@[kills double_positive_one] theorem double_positive_one_rejects_zero :
    ¬ (0 < (fun _ => 0) 1 → (fun _ => 0) 1 ≠ 0) := sorry

theorem double_kept (n : Nat) (h : double n = 0) (_x : PLift (h = h)) (_hk : n < 2) : n < 3 := sorry

@[kills double_kept] theorem double_kept_rejects_zero :
    ¬ ∀ (n : Nat) (h : (fun _ => 0) n = 0), PLift (h = h) → n < 2 → n < 3 := sorry

theorem double_kept_plain (n : Nat) (h : n = 0) (_x : PLift (h = h)) (_hk : double n < 2) : n < 3 := sorry

@[kills double_kept_plain] theorem double_kept_plain_rejects_zero :
    ¬ ∀ (n : Nat) (h : n = 0), PLift (h = h) → (fun _ => 0) n < 2 → n < 3 := sorry

end SoftwareChallengeTests.Fixtures.KeptChallenge

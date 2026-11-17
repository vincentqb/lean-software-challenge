module

public import SlowKills.CoreSpec
meta import SoftwareChallenge

public section

namespace SlowKills

def double : Nat → Nat := sorry

def triple : Nat → Nat := sorry

theorem double_correct (n : Nat) : double n = 2 * n := by
  sorry

theorem triple_correct (n : Nat) : triple n = 3 * n := by
  sorry

@[kills double_correct] theorem double_correct_rejects_identity : ¬ ∀ n : Nat, (fun n => n) n = 2 * n := by
  sorry

@[kills triple_correct] theorem triple_correct_rejects_identity : ¬ ∀ n : Nat, (fun n => n) n = 3 * n := by
  sorry

end SlowKills

module

public import SlowKills.CoreCode
meta import SoftwareChallenge

public section

namespace SlowKills

theorem double_correct (n : Nat) : double n = 2 * n := rfl

theorem triple_correct (n : Nat) : triple n = 3 * n := rfl

theorem double_correct_rejects_identity : ¬ ∀ n : Nat, (fun n => n) n = 2 * n := by
  have _slow : spin 200000 0 = 599994 := by decide +kernel
  intro h
  exact absurd (h 1) (by decide)

theorem triple_correct_rejects_identity : ¬ ∀ n : Nat, (fun n => n) n = 3 * n := by
  have _slow : spin 200001 0 = 599997 := by decide +kernel
  intro h
  exact absurd (h 1) (by decide)

end SlowKills

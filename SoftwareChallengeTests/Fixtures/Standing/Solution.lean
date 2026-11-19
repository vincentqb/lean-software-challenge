module

public import SoftwareChallengeTests.Fixtures.WorldSpec

public section

namespace SoftwareChallengeTests.Fixtures.Standing

def hole (n : Nat) : Nat := n

noncomputable def hole_lost (n : Nat) : Nat := n

theorem zero_right (m : Nat) : m + 0 = m := rfl

theorem zero_implicit {n : Nat} : n + 0 = n := rfl

set_option linter.defProp false in
def zero_kind (n : Nat) : n + 0 = n := rfl

theorem in_u.{v} (α : Sort v) (a : α) : a = a := rfl

theorem zero_flipped (n : Nat) : n = n + 0 := rfl

theorem zero_unsound (n : Nat) : n + 0 = n := by
  sorry

theorem succ_positive (_agrees : SuccAgrees nativeSucc) (n : Nat) : 0 < n + 1 := Nat.succ_pos n

theorem succ_correct (agrees : SuccAgrees nativeSucc) (n : Nat) : nativeSucc n = n + 1 := agrees n

end SoftwareChallengeTests.Fixtures.Standing

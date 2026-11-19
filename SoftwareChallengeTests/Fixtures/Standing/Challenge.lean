module

public import SoftwareChallengeTests.Fixtures.WorldSpec
meta import SoftwareChallenge

set_option warn.sorry false

public section

namespace SoftwareChallengeTests.Fixtures.Standing

noncomputable def hole : Nat → Nat := sorry

noncomputable def hole_lost : Nat → Nat := sorry

theorem zero_right (n : Nat) : n + 0 = n := sorry

theorem zero_implicit (n : Nat) : n + 0 = n := sorry

theorem zero_kind (n : Nat) : n + 0 = n := sorry

theorem in_u.{u} (α : Sort u) (a : α) : a = a := sorry

theorem zero_flipped (n : Nat) : n + 0 = n := sorry

theorem zero_absent (n : Nat) : n + 0 = n := sorry

theorem zero_outside (n : Nat) : n + 0 = n := sorry

theorem zero_unsound (n : Nat) : n + 0 = n := sorry

theorem first_is_zero : (⟨0, by omega⟩ : Fin 2).val = 0 := sorry

theorem succ_positive (agrees : SuccAgrees nativeSucc) (n : Nat) : 0 < n + 1 := sorry

theorem succ_correct (agrees : SuccAgrees nativeSucc) (n : Nat) : nativeSucc n = n + 1 := sorry

end SoftwareChallengeTests.Fixtures.Standing

module

public section

namespace Cases

theorem renamed (n : Nat) : n + 0 = n := by
  sorry

theorem implicit (n : Nat) : n * 1 = n := by
  sorry

theorem noIndexLeft (n : Nat) : no_index (n + 0) = n := by
  sorry

theorem noIndexRight (n : Nat) : n + 0 = n := by
  sorry

set_option cleanup.letToHave false in
theorem letHave (n : Nat) : (let m := n + 1; m = n + 1) := by
  sorry

def implemented (n : Nat) : Nat := sorry

theorem differs (n : Nat) : n + 0 = n := by
  sorry

theorem absent : 1 + 1 = 2 := by
  sorry

theorem outside : 2 + 2 = 4 := by
  sorry

theorem kind : 3 + 3 = 6 := by
  sorry

theorem universes.{u} (α : Sort u) (a : α) : a = a := by
  sorry

theorem axiomUsed : 4 + 4 = 8 := by
  sorry

def partialHole (n : Nat) : Nat := sorry

def mistyped (n : Nat) : Nat := sorry

theorem forgery : False := by
  sorry

theorem compiles : 5 + 5 = 10 := by
  sorry

end Cases

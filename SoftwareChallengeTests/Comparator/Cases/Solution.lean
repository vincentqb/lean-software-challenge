module

public section

namespace Cases

theorem renamed (k : Nat) : k + 0 = k := rfl

theorem implicit {n : Nat} : n * 1 = n := Nat.mul_one n

theorem noIndexLeft (n : Nat) : n + 0 = n := rfl

theorem noIndexRight (n : Nat) : no_index (n + 0) = n := rfl

theorem letHave (n : Nat) : (have m := n + 1; m = n + 1) := rfl

def implemented (n : Nat) : Nat := n

theorem differs (n : Nat) : 0 + n = n := Nat.zero_add n

set_option linter.defProp false in
def kind : 3 + 3 = 6 := rfl

theorem universes.{v} (α : Sort v) (a : α) : a = a := rfl

axiom cheat : 4 + 4 = 8

theorem axiomUsed : 4 + 4 = 8 := cheat

partial def partialHole (n : Nat) : Nat := if n = 0 then 0 else partialHole (n - 1)

def mistyped (n : Nat) : Int := n

end Cases

module

public import ConstantFolding.CoreCode
public import ConstantFolding.WorldSpec
meta import SoftwareChallenge

public section

namespace ConstantFolding

def evalNative (env : Nat → Nat) : Expr → Nat
  | .lit n => n
  | .var x => env x
  | .add a b => nativeAdd (evalNative env a) (evalNative env b)

theorem evalNative_eq (agrees : AddAgrees nativeAdd) (env : Nat → Nat) (e : Expr) :
    evalNative env e = eval env e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb =>
    simp only [evalNative, eval, ha, hb]
    exact agrees _ _

@[expose] def output (e : Expr) : String := toString (evalNative (fun _ => 0) (fold e))

private def run (e : Expr) : IO Unit := IO.println (output e)

Check AddAgrees nativeAdd : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71

Check AddAgrees nativeAdd := do
  for a in [0, 1, 2 ^ 64, 2 ^ 70] do
    for b in [7, 2 ^ 63] do
      unless nativeAdd a b - a == b do throw (IO.userError s!"nativeAdd {a} {b} disagrees")

end ConstantFolding

def main : IO Unit := ConstantFolding.run (.add (.lit 2) (.lit 3))

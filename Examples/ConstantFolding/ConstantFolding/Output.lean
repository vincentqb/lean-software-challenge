module

public import ConstantFolding.Fold
public import ConstantFolding.Native

public section

namespace ConstantFolding

def evalNative (env : Nat → Nat) : Expr → Nat
  | .lit n => n
  | .var x => env x
  | .add a b => nativeAdd (evalNative env a) (evalNative env b)

theorem evalNative_eq (env : Nat → Nat) (e : Expr) : evalNative env e = eval env e := by
  induction e with
  | lit n => rfl
  | var x => rfl
  | add a b ha hb =>
    simp only [evalNative, eval, ha, hb]
    exact addAgrees _ _

@[expose] def output (e : Expr) : String := toString (evalNative (fun _ => 0) (fold e))

end ConstantFolding

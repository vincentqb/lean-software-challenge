module

public import Examples.ConstantFolding.Core
public meta import SoftwareChallenge

public section

namespace Examples.ConstantFolding

@[expose] def output (e : Expr) : String := toString (evalNative (fun _ => 0) (fold e))

def run (e : Expr) : IO Unit := IO.println (output e)

@[exercises AddAgrees] def nativeAddSuite : IO Unit := do
  for a in [0, 1, 2 ^ 64, 2 ^ 70] do
    for b in [7, 2 ^ 63] do
      unless nativeAdd a b - a == b do throw (IO.userError s!"nativeAdd {a} {b} disagrees")

end Examples.ConstantFolding

def main : IO Unit := Examples.ConstantFolding.run (.add (.lit 2) (.lit 3))

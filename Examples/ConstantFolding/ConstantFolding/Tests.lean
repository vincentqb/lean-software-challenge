module

import ConstantFolding.Native
import SoftwareChallenge.Tests
meta import SoftwareChallenge

public section

namespace ConstantFolding

@[tests addAgrees] def addAgrees_beyond_64_bits : IO Unit :=
  unless nativeAdd (2 ^ 70) (2 ^ 70) == 2 ^ 71 do throw (IO.userError "nativeAdd (2 ^ 70) (2 ^ 70) is not 2 ^ 71")

@[tests addAgrees] def addAgrees_grid : IO Unit := do
  for a in [0, 1, 2 ^ 64, 2 ^ 70] do
    for b in [7, 2 ^ 63] do
      unless nativeAdd a b == a + b do throw (IO.userError s!"nativeAdd {a} {b} is not {a + b}")

end ConstantFolding

def main := SoftwareChallenge.testsMain

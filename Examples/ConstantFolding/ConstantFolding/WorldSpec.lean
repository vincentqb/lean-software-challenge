module

public import ConstantFolding.WorldSpec.NativeAdd
meta import SoftwareChallenge

public section

namespace ConstantFolding

WorldClaim AddAgrees (add : Nat → Nat → Nat) := ∀ a b, add a b = a + b

end ConstantFolding

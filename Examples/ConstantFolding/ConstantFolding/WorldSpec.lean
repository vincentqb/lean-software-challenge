module

public import ConstantFolding.WorldSpec.NativeAdd
meta import SoftwareChallenge

public section

namespace ConstantFolding

/-- The adder agrees with `Nat.add`. A different sum for any pair falsifies it. -/
WorldClaim AddAgrees (add : Nat → Nat → Nat) := ∀ a b, add a b = a + b

end ConstantFolding

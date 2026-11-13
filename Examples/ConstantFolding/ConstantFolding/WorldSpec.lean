module

meta import SoftwareChallenge

public section

namespace ConstantFolding

@[extern "lean_nat_add"] opaque nativeAdd : @& Nat → @& Nat → Nat

/-- The adder agrees with `Nat.add`. A different sum for any pair falsifies it. -/
WorldClaim AddAgrees (add : Nat → Nat → Nat) := ∀ a b, add a b = a + b

end ConstantFolding

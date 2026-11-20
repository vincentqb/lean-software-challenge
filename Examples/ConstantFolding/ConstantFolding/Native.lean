module

public section

namespace ConstantFolding

@[extern "lean_nat_add"] opaque nativeAdd : @& Nat → @& Nat → Nat

axiom addAgrees : ∀ a b, nativeAdd a b = a + b

end ConstantFolding

module

public section

namespace SoftwareChallengeTests.Fixtures.CoreCode.UnsafeTerm

def address (n : Nat) : Nat := unsafe (ptrAddrUnsafe n).toNat

end SoftwareChallengeTests.Fixtures.CoreCode.UnsafeTerm

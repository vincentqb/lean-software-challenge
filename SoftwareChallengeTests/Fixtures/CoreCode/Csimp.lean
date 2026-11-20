module

public section

namespace SoftwareChallengeTests.Fixtures.CoreCode.Csimp

def keep (n : Nat) : Nat := n

def bump (n : Nat) : Nat := n + 1

set_option linter.defProp false in
@[csimp] unsafe def keep_eq_bump : @keep = @bump := keep_eq_bump

end SoftwareChallengeTests.Fixtures.CoreCode.Csimp

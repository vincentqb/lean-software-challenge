module

public section

namespace SoftwareChallengeTests.Fixtures.CoreSpec.Replaced

inductive Side where
  | left
  | right (n : Nat)

def rightAfter (n : Nat) : Side := Side.right (n + 1)

attribute [implemented_by rightAfter] Side.right

end SoftwareChallengeTests.Fixtures.CoreSpec.Replaced

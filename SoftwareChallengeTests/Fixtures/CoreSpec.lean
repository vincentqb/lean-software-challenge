module

public section

namespace SoftwareChallengeTests.Fixtures

inductive Tree where
  | leaf
  | fork : Tree → Tree → Tree
  deriving Repr

end SoftwareChallengeTests.Fixtures

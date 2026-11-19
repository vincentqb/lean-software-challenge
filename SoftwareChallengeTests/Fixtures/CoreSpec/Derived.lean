module

public section

namespace SoftwareChallengeTests.Fixtures

inductive Forest where
  | grove (trees : List Forest)
  deriving BEq

end SoftwareChallengeTests.Fixtures

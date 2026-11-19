module

public section

namespace SoftwareChallengeTests.Fixtures.Corollary

theorem base (n : Nat) : n + 0 = n := rfl

private theorem bridge (n : Nat) : n + 0 + 0 = n := (congrArg (· + 0) (base n)).trans (base n)

theorem corollary (n : Nat) : n + 0 + 0 = n := bridge n

end SoftwareChallengeTests.Fixtures.Corollary

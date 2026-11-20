module

public import Native.WorldSpec.Twice
meta import SoftwareChallenge

public section

namespace Native

/-- `twice` doubles its argument. A value whose image is not twice it falsifies it. -/
WorldClaim TwiceDoubles (double : UInt32 → UInt32) := ∀ x, double x = 2 * x

end Native

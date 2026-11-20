module

public import Native.WorldSpec
meta import SoftwareChallenge

public section

namespace Native

Check TwiceDoubles twice := do
  unless twice 21 == 42 do throw (IO.userError s!"twice 21 is {twice 21}, not 42")

end Native

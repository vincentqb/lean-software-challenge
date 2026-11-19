module

meta import SoftwareChallenge.CoreCode.Graph

namespace SoftwareChallengeTests.Graph

meta section

open Lean SoftwareChallenge

def exactly (set : Std.HashSet Name) (members : List Name) : Bool :=
  set.size == members.length && members.all set.contains

def diamond : Graph := .ofEdges #[(`a, #[`b, `c]), (`b, #[`d]), (`c, #[`d]), (`e, #[`a])]

#guard exactly (diamond.closure #[`a]) [`a, `b, `c, `d]
#guard exactly (diamond.closure #[`e]) [`e, `a, `b, `c, `d]
#guard exactly (diamond.closure #[`b, `b, `c]) [`b, `c, `d]
#guard exactly (diamond.closure #[`z]) [`z]
#guard exactly (diamond.closure #[]) []

def cycle : Graph := .ofEdges #[(`a, #[`b]), (`b, #[`c]), (`c, #[`a, `c])]

#guard exactly (cycle.closure #[`b]) [`a, `b, `c]

def repeated : Graph := .ofEdges #[(`a, #[`b]), (`a, #[`c]), (`a, #[`b])]

#guard exactly (.ofArray (repeated.next `a)) [`b, `c]
#guard exactly (repeated.closure #[`a]) [`a, `b, `c]

#guard exactly (.ofArray (diamond.reverse.next `d)) [`b, `c]
#guard exactly (.ofArray (diamond.reverse.next `a)) [`e]
#guard (diamond.reverse.next `e).isEmpty

#guard (diamond.cut #[`b]).next `b == #[]
#guard (diamond.cut #[`b]).next `a == diamond.next `a
#guard exactly ((diamond.cut #[`b]).closure #[`a]) [`a, `b, `c, `d]
#guard exactly ((diamond.cut #[`b, `c]).closure #[`a]) [`a, `b, `c]
#guard exactly ((diamond.cut #[`z]).closure #[`e]) [`e, `a, `b, `c, `d]

#guard exactly (diamond.dependingOn #[`d]) [`a, `b, `c, `d, `e]
#guard exactly (diamond.dependingOn #[`b, `c]) [`a, `b, `c, `e]
#guard exactly (diamond.dependingOn #[`e]) [`e]
#guard exactly (diamond.dependingOn #[]) []

def numbered (index : Nat) : Name := .mkSimple s!"n{index}"

def complete (size : Nat) : Graph :=
  let nodes := (Array.range size).map numbered
  .ofEdges (nodes.map (·, nodes))

#guard exactly ((complete 40).closure #[numbered 7, numbered 7]) ((List.range 40).map numbered)

def chain (length : Nat) : Graph :=
  .ofEdges ((Array.range length).map fun index => (numbered index, #[numbered (index + 1)]))

#guard exactly ((chain 5000).closure #[numbered 0]) ((List.range 5001).map numbered)
#guard exactly ((chain 5000).dependingOn #[numbered 5000]) ((List.range 5001).map numbered)
#guard exactly ((chain 5000).closure #[numbered 4999]) [numbered 4999, numbered 5000]

def star (size : Nat) : Graph :=
  .ofEdges ((Array.range size).map fun index => (numbered index, #[`hub]))

#guard exactly ((star 20000).dependingOn #[`hub]) (`hub :: (List.range 20000).map numbered)
#guard exactly ((star 20000).closure #[numbered 3]) [numbered 3, `hub]

end

end SoftwareChallengeTests.Graph

module

public import SoftwareChallenge.CoreCode.Facts

public section

namespace SoftwareChallenge

inductive Next where
  | build | lint | test | comparator | replay
  | grade (commit : String)
  deriving BEq, Repr, Inhabited

structure Message where
  place : Place
  what : String
  why : String
  fix : String
  next : Next
  deriving BEq, Repr, Inhabited

end SoftwareChallenge

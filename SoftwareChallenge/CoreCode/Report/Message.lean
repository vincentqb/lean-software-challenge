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

def Next.command : Next → String
  | .build => "lake build"
  | .lint => "lake lint"
  | .test => "lake test"
  | .comparator => "lake comparator"
  | .replay => "lake script run software_challenge/replay"
  | .grade commit => s!"lake exe grade {commit}"

def Message.cite (place : Place) : String :=
  s!"{place.file}:{place.line}"

def Message.render (message : Message) : String :=
  s!"{Message.cite message.place}: {message.what}, {message.why}. {message.fix}, then run `{message.next.command}`."

end SoftwareChallenge

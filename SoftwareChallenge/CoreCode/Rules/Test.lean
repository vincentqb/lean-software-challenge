module

public import SoftwareChallenge.CoreCode.Facts

public section

namespace SoftwareChallenge

namespace Test

inductive Failure where
  | checkFailed (run : CheckRun)
  | counterexample (headline : Lean.Name) (inputs : String)
  | ownTest (run : OwnTestRun)
  | unknownOwnTest (name : String) (place : Place)
  deriving BEq, Repr, Inhabited

structure Result where
  failures : Array Failure
  timings : Array CheckRun
  sampled : Nat
  notSampled : Array SampleOutcome
  code : UInt32
  deriving BEq, Repr, Inhabited

end Test

end SoftwareChallenge

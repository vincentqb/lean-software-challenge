module

public import SoftwareChallenge.CoreSpec.Facts

@[expose] public section

namespace SoftwareChallenge

namespace Test

inductive Failure where
  | checkFailed (outcome : CheckOutcome)
  | counterexample (headline : Lean.Name) (inputs : String)
  | ownTest (run : OwnTestRun)
  | unknownOwnTest (name : String) (place : Place)
  deriving BEq, Repr, Inhabited

structure Result where
  failures : Array Failure
  timings : Array CheckOutcome
  sampled : Nat
  notSampled : Array SampleOutcome
  code : UInt32
  deriving BEq, Repr, Inhabited

end Test

structure Test.Complete (facts : TestFacts) : Prop where
  checksPass : ∀ outcome ∈ facts.checks, outcome.error? = none
  samplesHold : ∀ sample ∈ facts.samples, ∀ headline inputs, sample ≠ .counterexample headline inputs
  ownTestsPass : ∀ run ∈ facts.ownTests, run.code = 0
  ownTestsDeclared : facts.unknownOwnTests = #[]

end SoftwareChallenge

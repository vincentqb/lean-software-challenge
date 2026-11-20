module

public import SoftwareChallenge.CoreSpec.Facts

@[expose] public section

namespace SoftwareChallenge

namespace Test

inductive Failure where
  | checkFailed (outcome : CheckOutcome)
  | nativeCodeMissing (outcome : CheckOutcome) (declaration : String) (place : Place)
  | checkNotRun (check : CheckFact)
  | ownTest (run : OwnTestRun)
  | ownTestNotRun (test : OwnTestFact)
  | unknownOwnTest (name : String) (place : Place)
  deriving Inhabited

structure Result where
  failures : Array Failure
  timings : Array CheckOutcome
  code : UInt32

end Test

structure Test.Complete (facts : TestFacts) : Prop where
  checksRun : ∀ check ∈ facts.declaredChecks, ∃ outcome ∈ facts.checks, outcome.check = check
  checksPass : ∀ outcome ∈ facts.checks, outcome.error? = none
  ownTestsRun : ∀ test ∈ facts.declaredOwnTests, ∃ run ∈ facts.ownTests, run.test = test
  ownTestsPass : ∀ run ∈ facts.ownTests, run.code = 0
  ownTestsDeclared : facts.unknownOwnTests = #[]

end SoftwareChallenge

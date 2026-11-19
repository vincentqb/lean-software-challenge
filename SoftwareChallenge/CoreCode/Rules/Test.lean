module

public import SoftwareChallenge.CoreCode.Facts
public import SoftwareChallenge.CoreSpec.Test

public section

namespace SoftwareChallenge

open Lean

namespace Test

def samePlace (left right : Place) : Bool :=
  left.file == right.file && left.line == right.line

def sameCheck (left right : CheckFact) : Bool :=
  left.claim == right.claim && left.statement == right.statement && samePlace left.place right.place

def sameKind : OwnTestKind → OwnTestKind → Bool
  | .script, .script | .library, .library | .executable, .executable => true
  | _, _ => false

def sameOwnTest (left right : OwnTestFact) : Bool :=
  left.name == right.name && sameKind left.kind right.kind && samePlace left.place right.place

def failedChecks (facts : TestFacts) : Array Failure :=
  facts.checks.filterMap fun outcome => outcome.error?.map fun _ => .checkFailed outcome

def checksNotRun (facts : TestFacts) : Array Failure :=
  facts.declaredChecks.filterMap fun check =>
    if facts.checks.any (sameCheck ·.check check) then none else some (.checkNotRun check)

def failedOwnTests (facts : TestFacts) : Array Failure :=
  facts.ownTests.filterMap fun run => if run.code = 0 then none else some (.ownTest run)

def ownTestsNotRun (facts : TestFacts) : Array Failure :=
  facts.declaredOwnTests.filterMap fun test =>
    if facts.ownTests.any (sameOwnTest ·.test test) then none else some (.ownTestNotRun test)

def undeclaredOwnTests (facts : TestFacts) : Array Failure :=
  facts.unknownOwnTests.map fun name => .unknownOwnTest name ⟨"lakefile.lean", 1⟩

def failuresOf (facts : TestFacts) : Array Failure :=
  failedChecks facts ++ checksNotRun facts ++ failedOwnTests facts ++ ownTestsNotRun facts ++ undeclaredOwnTests facts

def Failure.code : Failure → UInt32
  | .ownTest run => run.code
  | _ => 1

def code (failures : Array Failure) : UInt32 :=
  let worst := failures.foldl (fun worst failure => max worst failure.code) 0
  if failures.isEmpty then 0 else if worst = 0 then 1 else worst

def slowestFirst (outcomes : Array CheckOutcome) : Array CheckOutcome :=
  outcomes.qsort (·.elapsed > ·.elapsed)

end Test

def Test.run (facts : TestFacts) : Test.Result :=
  let failures := Test.failuresOf facts
  { failures, timings := Test.slowestFirst facts.checks, code := Test.code failures }

end SoftwareChallenge

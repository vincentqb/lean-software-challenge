module

public import SoftwareChallenge.CoreCode.Rules.Statement
public import SoftwareChallenge.CoreCode.Rules.Lint
public import SoftwareChallenge.CoreCode.Rules.Test
public import SoftwareChallenge.CoreCode.Grade

public section

namespace SoftwareChallengeTests.Model

open Lean SoftwareChallenge

abbrev Mutation := Facts → Except String Facts

def after (facts : Facts) (writes : Statement.Writes) : Facts :=
  { facts with files := { facts.files with
      lock := (writes.lock?.map Decoded.decoded).getD facts.files.lock
      comparator := (writes.config?.map Decoded.decoded).getD facts.files.comparator } }

def relocked (facts : Facts) : Facts :=
  { facts with files := { facts.files with lock := .missing } }

def statement (facts : Facts) : Statement.Result :=
  Statement.run facts.lake facts.files facts.challenge

def targetNamed? (challenge : ChallengeFacts) (name : Name) : Option TargetFact :=
  challenge.targets.find? (·.constant.name == name)

def judge (challenge : ChallengeFacts) (config : Config) (solution : SolutionFacts) : Verdict :=
  let targets := (config.theorems ++ config.definitions).map (targetNamed? challenge)
  if targets.any (·.isNone) then .cannotJudge
  else if targets.all (·.any fun target => (solution.standingOf target).proved) then .accept
  else .refuse

def hidden (lake : LakeFacts) : Bool :=
  lake.packages.any (Sandbox.covers ·.real)

def comparator (base candidate : Facts) : Verdict :=
  match Statement.solution? base.lake, hidden base.lake with
  | some solution, false => judge base.challenge (Statement.configOf base.challenge solution) candidate.solution
  | _, _ => .cannotJudge

def testFacts (facts : Facts) (libraryPlace : Place) : TestFacts :=
  { declaredChecks := facts.solution.checks
    checks := facts.solution.checks.map fun check => { check, elapsed := 0, error? := none }
    declaredOwnTests := facts.lake.ownTests
    ownTests := facts.lake.ownTests.map fun test => { test, code := 0 }
    unknownOwnTests := facts.lake.testDriverArgs.filter fun name => !facts.lake.ownTests.any (·.name == name)
    testDriverArgsPlace := facts.lake.testDriverArgsPlace
    libraryPlace }

def decoded {α : Type} : Decoded α → Bool
  | .decoded _ => true
  | _ => false

def ownedUnchanged (base candidate : Facts) : Bool :=
  match base.files.lock with
  | .decoded locked => candidate.files.lock == base.files.lock &&
      locked.all fun entry => Lock.digestOf candidate.files.digests entry.path == some entry.digest
  | _ => false

def stepVerdict (code : UInt32) : Verdict :=
  if code == 0 then .accept else .refuse

structure Cells where
  build : UInt32
  lint : UInt32
  test : UInt32
  comparator : UInt32
  grade : UInt32
  deriving BEq, Repr, Inhabited

def Cells.list (cells : Cells) : List UInt32 :=
  [cells.build, cells.lint, cells.test, cells.comparator, cells.grade]

structure Row where
  name : String
  owner? : Option Mutation := none
  agent : Mutation := pure
  relocks : Bool := false
  compiles : Bool := true
  tests : TestFacts → Except String TestFacts := pure
  observed? : Option Verdict := none

structure Outcome where
  cells : Cells
  observations : List Observation
  base : Facts
  candidate : Facts

def Outcome.stopped? (outcome : Outcome) : Option Stage :=
  (outcome.observations.find? (·.verdict != .accept)).map (·.stage)

def observe (stage : Stage) (verdict : Verdict) : Observation :=
  { stage, verdict, detail := "" }

def evaluate (golden : Facts) (libraryPlace : Place) (row : Row) : Except String Outcome := do
  let base₀ ← match row.owner? with
    | some change => relocked <$> change golden
    | none => pure golden
  let baseResult := statement base₀
  let base := after base₀ baseResult.writes
  let changed ← row.agent base
  let candidate₀ := if row.relocks then relocked changed else changed
  let built := statement candidate₀
  let candidate := after candidate₀ built.writes
  let tested ← row.tests (testFacts candidate libraryPlace)
  let compiled := fun (code : UInt32) => if row.compiles then code else 1
  let build := compiled built.code
  let lint := compiled (Lint.run candidate).code
  let test := compiled (Test.run tested).code
  let judged := row.observed?.getD (if row.compiles then comparator base candidate else .cannotJudge)
  let stated := baseResult.code == 0 && decoded base.files.lock && decoded base.files.comparator
  let observations := [observe .lock .accept, observe .statement (if stated then .accept else .cannotJudge),
    observe .owned (if ownedUnchanged base candidate then .accept else .refuse),
    observe .dependencies (if hidden base.lake then .cannotJudge else .accept), observe .worktree .accept,
    observe .build (stepVerdict build), observe .lint (stepVerdict lint), observe .test (stepVerdict test),
    observe .comparator judged]
  return { cells := { build, lint, test, comparator := judged.code, grade := (Grade.decide observations).code }
           observations, base, candidate }

end SoftwareChallengeTests.Model

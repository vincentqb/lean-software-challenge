import SoftwareChallengeTests.Guards
import SoftwareChallengeTests.Runs

namespace SoftwareChallengeTests

open Lean

structure Outcome where
  name : String
  failure? : Option String
  shown : String
  elapsed : Nat

def timed (name : String) (check : ExceptT String IO String) : IO Outcome := do
  let start ← IO.monoMsNow
  let result ← try check.run catch error => pure (.error s!"stopped on `{error}`")
  let elapsed := (← IO.monoMsNow) - start
  return match result with
    | .ok shown => { name, failure? := none, shown, elapsed }
    | .error failure => { name, failure? := some failure, shown := "", elapsed }

def pool (jobs : Nat) (tasks : Array (IO Outcome)) : IO (Array Outcome) := do
  let next ← IO.mkRef 0
  let done ← IO.mkRef (#[] : Array (Nat × Outcome))
  let worker : IO Unit := do
    repeat
      let index ← next.modifyGet fun index => (index, index + 1)
      let some task := tasks[index]? | break
      let outcome ← task
      done.modify (·.push (index, outcome))
  let workers ← (List.range (min jobs tasks.size)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for worker in workers do IO.ofExcept worker.get
  return ((← done.get).qsort (·.1 < ·.1)).map (·.2)

def seconds (ms : Nat) : String := s!"{ms / 1000}.{ms % 1000 / 100} s"

def run (lsc : System.FilePath) : IO UInt32 := do
  let start ← IO.monoMsNow
  let context : Context := { lsc, root := lsc / ".lake" / "build" / "tests" }
  IO.FS.createDirAll context.root
  let env ← importModules #[{ module := `SoftwareChallenge.Problem }] {}
  let some (.inductInfo rule) := env.find? ``SoftwareChallenge.Rule | throw (.userError "SoftwareChallenge.Rule is missing")
  let quiet := fun (check : ExceptT String IO Unit) => do check; return ""
  let runs ← IO.asTask (prio := .dedicated) <| pool 6 <|
    #[timed "grade accepts the printed fix of a SHA candidate" (gradeRun context),
      timed "template run" (templateRun context), timed "coverage" (quiet (coverageRun context))] ++
    fixtures.toArray.map fun fixture =>
      let name := (rule.ctors[fixture.rule.ctorIdx]?.map (·.getString!)).getD "rule"
      timed s!"rule {name}" (quiet (fixtureRun context fixture name))
  let guards ← [timed s!"library within {lineBudget} lines" (quiet (withinBudget lsc)),
    timed "no dead code" (quiet noDeadCode), timed "one fixture per rule" (quiet (onePerRule rule))].mapM id
  let outcomes := (← IO.ofExcept runs.get) ++ guards.toArray
  for outcome in outcomes do
    IO.println s!"{if outcome.failure?.isSome then "FAILED" else "held  "} {outcome.name}  {seconds outcome.elapsed}"
    unless outcome.shown.isEmpty do IO.println ("  " ++ outcome.shown.replace "\n" "\n  ")
  for outcome in outcomes do
    if let some failure := outcome.failure? then IO.eprintln s!"FAILED {outcome.name}: {failure}"
  let failed := (outcomes.filter (·.failure?.isSome)).size
  IO.println s!"{outcomes.size - failed} of {outcomes.size} checks held in {seconds ((← IO.monoMsNow) - start)}"
  return if failed == 0 then 0 else 1

end SoftwareChallengeTests

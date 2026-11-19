module

public meta import Lean
public meta import SoftwareChallenge.Commands.Extensions

public section
meta section

open Lean Elab Command

namespace SoftwareChallenge

structure CheckOutcome where
  file : String
  line : Nat
  claim : Name
  elapsed : Nat
  error : Option String

def checkJobs : IO Nat := do
  let threads := min 16 (System.Platform.Internal.getHardwareConcurrency ()).toNat
  return max 1 (((← IO.getEnv "SOFTWARE_CHALLENGE_JOBS").bind (·.toNat?)).getD threads)

def concurrently (actions : Array (IO Unit)) (jobs : Nat) : IO (Array (Nat × Except IO.Error Unit)) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (#[] : Array (Nat × Nat × Except IO.Error Unit))
  let worker : IO Unit := do
    repeat
      let index ← next.modifyGet fun index => (index, index + 1)
      let some action := actions[index]? | break
      let start ← IO.monoMsNow
      let outcome ← action.toBaseIO
      results.modify (·.push (index, (← IO.monoMsNow) - start, outcome))
  let workers ← (List.range (min actions.size (max 1 jobs))).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for task in workers do IO.ofExcept task.get
  return ((← results.get).qsort (·.1 < ·.1)).map fun (_, elapsed, outcome) => (elapsed, outcome)

def runAllChecks (modules : Array (Name × String)) (jobs : Option Nat := none) : CoreM (Array CheckOutcome) := do
  let env ← getEnv
  let mut found := #[]
  for evidence in allEvidence env do
    let some index := env.getModuleIdxFor? evidence.source | continue
    let module := env.header.modules[index.toNat]!.module
    let some (_, file) := modules.find? (·.1 == module) | continue
    found := found.push (file, evidence, ← unsafe evalConst (IO Unit) evidence.source)
  let planned := found.qsort fun (a, x, _) (b, y, _) => a < b || a == b && x.line < y.line
  let outcomes ← concurrently (planned.map (·.2.2)) (jobs.getD (← checkJobs))
  return (planned.zip outcomes).map fun ((file, evidence, _), (elapsed, outcome)) => {
    file, line := evidence.line, claim := evidence.claim, elapsed
    error := match outcome with
      | .ok _ => none
      | .error error => some (toString error) }

def CheckOutcome.failure? (run : CheckOutcome) : Option String :=
  run.error.map fun error => s!"{run.file}:{run.line}: the Check of {run.claim} failed: {error}. A Check tests a \
    world claim against the real foreign code, so either the Check is wrong or {run.claim} is false. Fix the Check; \
    if {run.claim} is false, the statement assumes something false: remove {run.claim} from the headlines of \
    Challenge.lean and from its WorldSpec module, delete owned.lock, and run `lake build` to record the new \
    statement. Then run `lake test`."

def timings (runs : Array CheckOutcome) : Array String :=
  (runs.qsort (·.elapsed > ·.elapsed)).map fun run =>
    s!"{run.file}:{run.line} {run.claim}  {run.elapsed / 1000}.{run.elapsed % 1000 / 100} s"

def checkFailures (modules : Array (Name × String)) (jobs : Option Nat := none) : CoreM (Array String) :=
  return (← runAllChecks modules jobs).filterMap (·.failure?)

def runChecks (modules : Array (Name × String)) : CommandElabM Unit := do
  let runs ← liftCoreM (runAllChecks modules)
  for line in timings runs do IO.println line
  let failures := runs.filterMap (·.failure?)
  unless failures.isEmpty do throwError ("\n".intercalate failures.toList)

end SoftwareChallenge

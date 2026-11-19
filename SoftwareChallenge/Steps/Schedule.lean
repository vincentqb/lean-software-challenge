module

public section

namespace SoftwareChallenge.Steps

def jobsAllowed : IO Nat := do
  let threads := min 16 (System.Platform.Internal.getHardwareConcurrency ()).toNat
  return max 1 (((← IO.getEnv "SOFTWARE_CHALLENGE_JOBS").bind (·.toNat?)).getD threads)

def schedule {α β : Type} (jobs : Nat) (tasks : Array α) (runner : α → IO β) : IO (Array (β × Nat)) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (#[] : Array (Nat × β × Nat))
  let worker : IO Unit := do
    repeat
      let index ← next.modifyGet fun index => (index, index + 1)
      let some task := tasks[index]? | break
      let start ← IO.monoMsNow
      let value ← runner task
      let elapsed := (← IO.monoMsNow) - start
      results.modify (·.push (index, value, elapsed))
  let workers ← (List.range (min tasks.size (max 1 jobs))).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for task in workers do IO.ofExcept task.get
  return ((← results.get).qsort (·.1 < ·.1)).map (·.2)

def tenths (milliseconds : Nat) : String := s!"{milliseconds / 1000}.{milliseconds % 1000 / 100} s"

end SoftwareChallenge.Steps

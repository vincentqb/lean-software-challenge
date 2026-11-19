module

public meta import Lean
public meta import SoftwareChallenge.Commands.Extensions
public meta import SoftwareChallenge.Read.Lake
public meta import SoftwareChallenge.Read.Constants
public meta import SoftwareChallenge.Steps.Schedule

public section
meta section

open Lean Elab Command

namespace SoftwareChallenge

deriving instance ToJson, FromJson for CheckFact
deriving instance ToJson, FromJson for CheckOutcome

namespace Steps.Checks

structure Ran where
  declared : Array CheckFact
  outcomes : Array CheckOutcome
  finished : Bool
  deriving ToJson, FromJson

def declared (modules : Array (Name × String)) : MetaM (Array (Evidence × CheckFact)) := do
  let env ← getEnv
  modules.flatMapM fun (module, file) => do
    let some index := env.getModuleIdx? module | return #[]
    (PersistentEnvExtension.getModuleEntries evidenceExt env index).mapM fun evidence => do
      return (evidence, { claim := evidence.claim, statement := ← Read.shown evidence.statement
                          place := { file, line := evidence.line } })

def actionOf (evidence : Evidence) : CoreM (IO Unit) := do
  try unsafe evalConst (IO Unit) evidence.source
  catch failure => let shown ← failure.toMessageData.toString; return throw (IO.userError shown)

def run (out : String) (modules : Array (Name × String)) : CommandElabM Unit := do
  let found ← liftTermElabM (declared modules)
  let write := fun (ran : Ran) => IO.FS.writeFile out (toJson ran).compress
  write { declared := found.map (·.2), outcomes := #[], finished := false }
  let actions ← liftCoreM <| found.mapM fun (evidence, check) => return (check, ← actionOf evidence)
  let results ← schedule (← jobsAllowed) actions fun (_, action) => action.toBaseIO
  let errorOf : Except IO.Error Unit → Option String
    | .ok () => none
    | .error failure => some (toString failure)
  write { declared := found.map (·.2), finished := true
          outcomes := (actions.zip results).map fun ((check, _), (result, elapsed)) =>
            { check, elapsed, error? := errorOf result } }

end SoftwareChallenge.Steps.Checks

module

public meta import Lean

public section
meta section

open Lean Elab Command

namespace SoftwareChallenge

structure Evidence where
  claim : Name
  statement : Expr
  source : Name
  line : Nat

initialize claimsExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

initialize evidenceExt : SimplePersistentEnvExtension Evidence (Array Evidence) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

initialize killsExt : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

initialize terminatesExt : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

initialize witnessExt : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

syntax (name := Link.kills) "kills " ident : attr

syntax (name := Link.terminates) "terminates " ident : attr

syntax (name := Link.witness) "witness " ident : attr

private def link (ext : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name))) (name : Name)
    (descr : String) : IO Unit := registerBuiltinAttribute {
  name, descr
  add := fun declaration stx _ => do
    let target ← realizeGlobalConstNoOverloadWithInfo stx[1]
    modifyEnv (ext.addEntry · (declaration, target)) }

initialize link killsExt `kills "marks a theorem of the challenge as a kill of the headline it names"

initialize link terminatesExt `terminates "marks a headline as stating that the partial_fixpoint hole it names returns"

initialize link witnessExt `witness "marks a theorem of the challenge as a witness that some input meets the preconditions of the headline it names"

def isWorldClaim (env : Environment) (name : Name) : Bool := (claimsExt.getState env).contains name

def conclusionHead : Expr → Name
  | .forallE _ _ body _ => conclusionHead body
  | .mdata _ expr => conclusionHead expr
  | conclusion => conclusion.getAppFn.constName

def allEvidence (env : Environment) : Array Evidence := evidenceExt.getState env

def premisesEntry : String := "softwareChallenge.premises"

partial def premiseUses (env : Environment) (type value : Expr) (index : Nat := 0) : Array (Nat × Bool) :=
  match type.consumeMData, value.consumeMData with
  | .forallE _ binder rest _, .lam _ _ body _ =>
    let later := premiseUses env rest body (index + 1)
    if isWorldClaim env (conclusionHead binder) then #[(index, body.hasLooseBVar 0)] ++ later else later
  | _, _ => #[]

def premisesLinter : Linter where
  name := `SoftwareChallenge.premisesLinter
  run _ := do
    let env := (← getEnv).setExporting false
    let mut seen : NameSet := {}
    for tree in ← getInfoTrees do
      for name in Linter.getNewDecls tree do
        if seen.contains name then continue
        seen := seen.insert name
        let some (.thmInfo info) := env.find? name | continue
        let uses := (premiseUses env info.type info.value).foldl (init := {})
          fun (uses : Std.TreeMap String Float) (index, used) =>
            uses.insert (toString index) (if used then 1 else 0)
        Linter.logCodeQualityEntry
          { name := premisesEntry, source := .declaration env.mainModule name, value := .dict uses }

initialize addLinter premisesLinter

def premiseRecord? (env : Environment) (module theoremName : Name) : Option (Array (Nat × Bool)) := do
  let index ← env.getModuleIdx? module
  let entries := Linter.codeQualityLogExt.getModuleEntries env index (level := .server)
  let found ← entries.findSome? fun logged => match logged.entry with
    | { name, source := .declaration _ declared, value := .dict uses } =>
      if name == premisesEntry && declared == theoremName then some uses else none
    | _ => none
  return found.toArray.filterMap fun (index, used) => index.toNat?.map (·, used != 0)

private def checked (cmd : Syntax) : CommandElabM Unit := do
  let errors := fun (messages : MessageLog) =>
    (messages.toList.filter (·.severity == .error)).length
  let before := errors (← get).messages
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    elabCommand cmd
  if errors (← get).messages > before then
    throwError "declaration failed to elaborate, as the errors above say. Fix them, then run `lake build`."

elab doc?:(docComment)? "WorldClaim " n:ident bs:(ppSpace bracketedBinder)* " := " t:term : command => do
  unless doc?.isSome do
    throwError "WorldClaim {n} has no doc comment, but a reviewer judges a world claim by the observation that \
      would falsify it. Add `/-- <that observation> -/` above `WorldClaim {n}`, then run `lake build`."
  checked (← `($[$doc?]? @[expose, reducible] public def $n $bs* : Prop := $t))
  let name ← resolveGlobalConstNoOverload n
  modifyEnv (claimsExt.addEntry · name)

private def shown (term : Term) : CoreM String :=
  return (← PrettyPrinter.ppTerm term).pretty 100000

private def claimOf (claim : Term) : CommandElabM (Name × Expr) := liftTermElabM do
  let written ← shown claim
  let statement ← Term.elabTerm claim none
  Term.synthesizeSyntheticMVarsNoPostponing
  let statement ← instantiateMVars statement
  let head := statement.getAppFn.constName
  unless isWorldClaim (← getEnv) head do
    throwError "`{written}` is not a WorldClaim, so this Check would test nothing a headline assumes. Name a claim \
      declared with `WorldClaim` in a WorldSpec module, as in `Check <claim> <its arguments> := …`, then run \
      `lake build`."
  let type ← Meta.whnf (← Meta.inferType statement)
  unless type.isProp do
    let missing ← Meta.forallTelescope type fun binders _ => binders.mapM fun binder => do
      return (← binder.fvarId!.getUserName, (← Meta.ppExpr (← Meta.inferType binder)).pretty 100000)
    let listed := ", ".intercalate (missing.map fun (name, type) => s!"`({name} : {type})`").toList
    let filled := " ".intercalate (missing.map fun (name, _) => s!"({name} := …)").toList
    throwError "`{written}` is a WorldClaim that takes {missing.size} more \
      {if missing.size == 1 then "argument" else "arguments"}, {listed}, so this Check states no proposition. \
      Write `Check {written} {filled} := …`, with the arguments the headlines assume it of, then run `lake build`."
  if statement.hasMVar then
    throwError "`{written}` leaves an argument unstated, so the Check would not test one definite statement: give \
      every argument of the claim, replacing each `_` with a term, then run `lake build`."
  return (head, statement)

private partial def inputsHeld (statement : Expr) : MetaM Expr := do
  match statement with
  | .forallE name type body _ =>
    if ← Meta.isProp type then return statement
    inputsHeld (body.instantiate1 (← Meta.mkFreshExprMVar type (userName := name)))
  | _ => return statement

private def instanceTemplate (statement : Expr) : MetaM String := do
  let unfolded := (← Meta.unfoldDefinition? statement).getD statement
  return (← Meta.ppExpr (← inputsHeld (← Meta.whnfR unfolded))).pretty 100000

private def register (claim : Name × Expr) (action : Term) : CommandElabM Unit := do
  let env ← getEnv
  let base := claim.1 ++ env.mainModule
  let mut index := 1
  while env.contains (base ++ Name.mkSimple s!"check_{index}") do
    index := index + 1
  let source := base ++ Name.mkSimple s!"check_{index}"
  checked (← `(public def $(mkIdent (rootNamespace ++ source)) : IO Unit := $action))
  let line := (← getRefPosition).line
  modifyEnv (evidenceExt.addEntry · { claim := claim.1, statement := claim.2, source, line })

elab "Check " claim:term " : " inst:term : command => do
  let found ← claimOf claim
  let messages := (← get).messages
  try checked (← `(example : $claim → $inst := fun h => by first | exact h | apply h))
  catch _ =>
    modify ({ · with messages })
    let claimed ← liftCoreM (shown claim)
    let stated ← liftCoreM (shown inst)
    let template ← liftTermElabM (instanceTemplate found.2)
    throwError "`{stated}` is not an instance of `{claimed}`, so the Check would test something the claim does not \
      imply. State `{claimed}` at concrete values, as in `Check {claimed} : {template}` with each `?` replaced by a \
      value, then run `lake build`."
  let falsified := Syntax.mkStrLit s!"{← liftCoreM (shown inst)} is false"
  register found (← `(unless decide ($inst) do throw (IO.userError $falsified)))

elab "Check " claim:term " := " action:term : command => do
  register (← claimOf claim) action

structure CheckRun where
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

def runAllChecks (modules : Array (Name × String)) (jobs : Option Nat := none) : CoreM (Array CheckRun) := do
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

def CheckRun.failure? (run : CheckRun) : Option String :=
  run.error.map fun error => s!"{run.file}:{run.line}: the Check of {run.claim} failed: {error}. A Check tests a \
    world claim against the real foreign code, so either the Check is wrong or {run.claim} is false. Fix the Check; \
    if {run.claim} is false, the statement assumes something false: remove {run.claim} from the headlines of \
    Challenge.lean and from its WorldSpec module, delete owned.lock, and run `lake build` to record the new \
    statement. Then run `lake test`."

def timings (runs : Array CheckRun) : Array String :=
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

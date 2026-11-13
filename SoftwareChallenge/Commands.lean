module

public meta import SoftwareChallenge.Policy
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

def isWorldClaim (env : Environment) (name : Name) : Bool := (claimsExt.getState env).contains name

def allEvidence (env : Environment) : Array Evidence := evidenceExt.getState env

private def checked (cmd : Syntax) : CommandElabM Unit := do
  let errors := fun (messages : MessageLog) =>
    (messages.toList.filter (·.severity == .error)).length
  let before := errors (← get).messages
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    elabCommand cmd
  if errors (← get).messages > before then throwError "declaration failed to elaborate"

elab doc?:(docComment)? "WorldClaim " n:ident bs:(ppSpace bracketedBinder)* " := " t:term : command => do
  unless doc?.isSome do
    throwError "WorldClaim {n} needs a doc comment naming the observation that would falsify it"
  checked (← `($[$doc?]? @[expose, reducible] public def $n $bs* : Prop := $t))
  let name ← resolveGlobalConstNoOverload n
  modifyEnv (claimsExt.addEntry · name)

private def claimOf (claim : Term) : CommandElabM (Name × Expr) := liftTermElabM do
  let statement ← Term.elabTermEnsuringType claim (mkSort .zero)
  Term.synthesizeSyntheticMVarsNoPostponing
  let statement ← instantiateMVars statement
  let head := statement.getAppFn.constName
  unless isWorldClaim (← getEnv) head do throwError "{claim} is not a WorldClaim"
  if statement.hasMVar then throwError "{claim}: give every argument of the claim"
  return (head, statement)

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
    throwError "{inst} is not an instance of {claim}"
  let falsified := Syntax.mkStrLit s!"{← liftCoreM (PrettyPrinter.ppTerm inst)} is false"
  register found (← `(unless decide ($inst) do throw (IO.userError $falsified)))

elab "Check " claim:term " := " action:term : command => do
  register (← claimOf claim) action

def checkFailures (modules : Array Name) : CoreM (Array String) := do
  let env ← getEnv
  let mut failures := #[]
  for evidence in allEvidence env do
    let some index := env.getModuleIdxFor? evidence.source | continue
    let module := env.header.modules[index.toNat]!.module
    unless modules.contains module do continue
    let action ← unsafe evalConst (IO Unit) evidence.source
    if let .error error ← action.toBaseIO then
      failures := failures.push s!"{module}, line {evidence.line}: the Check of {evidence.claim} failed: \
        {error}; fix the check, or tell the owner that {evidence.claim} is false"
  return failures

def runChecks (modules : Array Name) : CommandElabM Unit := do
  let failures ← liftCoreM (checkFailures modules)
  unless failures.isEmpty do throwError ("\n".intercalate failures.toList)

end SoftwareChallenge

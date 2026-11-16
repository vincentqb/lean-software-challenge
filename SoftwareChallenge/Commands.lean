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

def allEvidence (env : Environment) : Array Evidence := evidenceExt.getState env

def premisesEntry : String := "softwareChallenge.premises"

partial def premiseUses (env : Environment) (type value : Expr) (index : Nat := 0) : Array (Nat × Bool) :=
  match type.consumeMData, value.consumeMData with
  | .forallE _ binder rest _, .lam _ _ body _ =>
    let later := premiseUses env rest body (index + 1)
    if isWorldClaim env binder.getAppFn.constName then #[(index, body.hasLooseBVar 0)] ++ later else later
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

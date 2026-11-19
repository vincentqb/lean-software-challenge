module

public meta import Lean
public meta import SoftwareChallenge.Commands.WorldClaim

public section
meta section

open Lean Elab Command

namespace SoftwareChallenge

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
  elabOrFail (← `(public def $(mkIdent (rootNamespace ++ source)) : IO Unit := $action))
  let line := (← getRefPosition).line
  modifyEnv (evidenceExt.addEntry · { claim := claim.1, statement := claim.2, source, line })

elab "Check " claim:term " : " inst:term : command => do
  let found ← claimOf claim
  let messages := (← get).messages
  try elabOrFail (← `(example : $claim → $inst := fun h => by first | exact h | apply h))
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

end SoftwareChallenge

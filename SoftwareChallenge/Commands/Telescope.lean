module

public meta import Lean
public meta import SoftwareChallenge.CoreSpec.Role
public meta import SoftwareChallenge.CoreSpec.Telescope
public meta import SoftwareChallenge.Commands.Extensions

public section
meta section

open Lean Meta

namespace SoftwareChallenge.Telescope

def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

def roleOf (env : Environment) (name : Name) : Role := Role.ofName (moduleOf env name)

def isForeign (env : Environment) (name : Name) : Bool :=
  isExtern env name && roleOf env name == .worldSpec

def isLocalHole (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).isNone && !name.isInternal && match env.find? name with
    | some (.defnInfo info) => info.value.hasSorry
    | some (.opaqueInfo info) => info.value.hasSorry
    | _ => false

def replaceableHere (env : Environment) (name : Name) : Bool := isLocalHole env name || isForeign env name

private def abbreviates (name : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo info) := env.find? name | return false
  unless !isWorldClaim env name && roleOf env name matches .coreSpec | .worldSpec do return false
  forallTelescopeReducing info.type fun _ result => return (← whnf result).isProp

partial def unfolded (type : Expr) : MetaM Expr :=
  forallTelescope type fun binders body => do
    let body := body.consumeMData
    let .const name _ := body.getAppFn | return type
    unless ← abbreviates name do return type
    let some expanded ← delta? body (· == name) | return type
    mkForallFVars binders (← unfolded expanded)

def summarize (replaceable : Name → Bool) (binders : Array Expr) : MetaM (Array Binder) := do
  let env ← getEnv
  let types ← binders.mapM inferType
  let mut summary := #[]
  for (binder, index) in binders.zipIdx do
    let type := types[index]!
    let meaning ← unfolded type
    let depended := (types.extract (index + 1) types.size).any (·.containsFVar binder.fvarId!)
    let prop ← isProp type
    let kind := if depended || !prop then BinderKind.input
      else if isWorldClaim env (conclusionHead meaning) then .claim
      else .precondition
    summary := summary.push {
      kind, prop
      mentions := meaning.getUsedConstants.any replaceable
      refers := (List.range index).filter fun earlier => type.containsFVar binders[earlier]!.fvarId! }
  return summary

def witnessStatement (binders : Array Expr) (summary : Array Binder) : MetaM Expr := do
  let kept := kept summary.toList
  let premised := fun (index : Nat) => summary[index]!.kind == .claim && summary[index]!.refers.isEmpty
  let conditions := kept.filter fun index => summary[index]!.kind != .input && !premised index
  let mut statement := mkAndN (← conditions.mapM fun index => inferType binders[index]!)
  for index in (kept.filter (summary[·]!.kind == .input)).reverse do
    let binder := binders[index]!
    let type ← inferType binder
    statement := mkApp2 (.const ``Exists [(← getLevel type).normalize]) type
      (.lam (← binder.fvarId!.getUserName).eraseMacroScopes type (statement.abstract #[binder]) .default)
  for index in (kept.filter premised).reverse do
    statement := .forallE (← binders[index]!.fvarId!.getUserName) (← inferType binders[index]!) statement .default
  return statement

def witnessType (replaceable : Name → Bool) (type : Expr) : MetaM (Option Expr) := do
  forallTelescope (← unfolded type) fun binders _ => do
    let summary ← summarize replaceable binders
    unless needsWitness summary.toList do return none
    return some (← witnessStatement binders summary)

end SoftwareChallenge.Telescope

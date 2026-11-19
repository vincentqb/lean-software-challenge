module

public meta import Lean
public meta import SoftwareChallenge.Commands.Extensions

public section
meta section

open Lean Elab Command

namespace SoftwareChallenge

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

end SoftwareChallenge

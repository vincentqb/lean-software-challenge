module

public meta import Lean
public meta import SoftwareChallenge.Commands.Extensions

public section
meta section

open Lean Elab Command

namespace SoftwareChallenge

def elabOrFail (cmd : Syntax) : CommandElabM Unit := do
  let errors := fun (messages : MessageLog) =>
    (messages.toList.filter (·.severity == .error)).length
  let before := errors (← get).messages
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    elabCommand cmd
  if errors (← get).messages > before then
    throwError "declaration failed to elaborate, as the errors above say. Fix them, then run `lake build`."

elab doc?:(docComment)? "WorldClaim " n:ident bs:(ppSpace bracketedBinder)* " := " t:term : command => do
  elabOrFail (← `($[$doc?]? @[expose, reducible] public def $n $bs* : Prop := $t))
  let name ← resolveGlobalConstNoOverload n
  modifyEnv (claimsExt.addEntry · name)

end SoftwareChallenge

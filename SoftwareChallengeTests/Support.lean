module

public meta import SoftwareChallenge.Commands

public section
meta section

open Lean Elab Command SoftwareChallenge

namespace SoftwareChallengeTests

elab "rejects " reason:str " in " cmd:command : command => do
  let saved ← get
  let oldCount := saved.messages.toList.length
  let mut diagnostics : Array String := #[]
  try
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      elabCommand cmd
    for message in (← get).messages.toList.drop oldCount do
      if message.severity == .error then
        diagnostics := diagnostics.push (← message.data.toString)
  catch error =>
    diagnostics := diagnostics.push (← error.toMessageData.toString)
  set saved
  unless diagnostics.any (fun text => (text.splitOn reason.getString).length > 1) do
    throwError "Expected rejection containing {reason.getString}, got {diagnostics}"

elab "assert_evidence " n:ident " = " checks:num " checks" : command => do
  let name ← resolveGlobalConstNoOverload n
  let found := ((allEvidence (← getEnv)).filter (·.claim == name)).size
  unless found == checks.getNat do throwError "{name}: {found} checks"

end SoftwareChallengeTests

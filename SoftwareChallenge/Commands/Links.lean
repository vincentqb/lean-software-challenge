module

public meta import Lean
public meta import SoftwareChallenge.Commands.Telescope

public section
meta section

open Lean Elab Meta

namespace SoftwareChallenge

syntax (name := Link.kills) "kills " ident : attr

syntax (name := Link.terminates) "terminates " ident : attr

def witnessName (headline : Name) : Name := headline.appendAfter "_applies"

private def deriveWitness (headline : Name) (ref : Syntax) : CoreM Unit := do
  let name := witnessName headline
  let env := (← getEnv).setExporting false
  unless (env.getModuleIdxFor? headline).isNone && !env.contains name do return
  let some found := env.findAsync? headline | return
  unless found.kind matches .thm do return
  if (localLinks env .kills ++ localLinks env .witness).any (·.1 == headline) then return
  let signature := found.sig.get
  let derived ← withoutExporting <| MetaM.run' do
    let some type ← Telescope.witnessType (Telescope.replaceableHere env) signature.type | return none
    return some (type, ← mkSorry type false)
  let some (type, value) := derived | return
  let used := (collectLevelParams {} type).params
  addDecl (.thmDecl { name, levelParams := signature.levelParams.filter used.contains, type, value })
  addDeclarationRangesFromSyntax name ref
  modifyEnv (linksExt.addEntry · { kind := .witness, source := name, target := headline })

initialize registerBuiltinAttribute {
  name := `kills
  descr := "marks a theorem of the challenge as a kill of the headline it names, and on the headline's first kill \
    derives the theorem that some input meets the headline's preconditions"
  add := fun declaration stx _ => do
    let target ← realizeGlobalConstNoOverloadWithInfo stx[1]
    modifyEnv (linksExt.addEntry · { kind := .kills, source := declaration, target })
    try deriveWitness target stx
    catch problem =>
      let line := ((← findDeclarationRanges? target).map (·.selectionRange.pos.line)).getD 0
      logWarning m!"`@[kills {target}]` could not derive {witnessName target}, the theorem that some input meets \
        the preconditions of {target} (line {line}), because {problem.toMessageData}, so nothing would show that \
        {target} is not vacuous. State each precondition of {target} as a hypothesis of its own, delete owned.lock \
        if there is one, then run `lake build`." }

initialize registerBuiltinAttribute {
  name := `terminates
  descr := "marks a headline as stating that the partial_fixpoint hole it names returns"
  add := fun declaration stx _ => do
    let target ← realizeGlobalConstNoOverloadWithInfo stx[1]
    modifyEnv (linksExt.addEntry · { kind := .terminates, source := declaration, target }) }

end SoftwareChallenge

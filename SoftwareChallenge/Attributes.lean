module

public meta import Lean
public import SoftwareChallenge.Tests

public section
meta section

open Lean Elab Meta Term

namespace SoftwareChallenge

inductive LinkKind where
  | kills | witness | terminates | consistent | tests
  deriving BEq

structure Link where
  kind : LinkKind
  source : Name
  target : Name

initialize linksExt : SimplePersistentEnvExtension Link (Array Link) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

def links (env : Environment) (kind : LinkKind) : Array (Name × Name) :=
  ((linksExt.getState env).filter (·.kind == kind)).map fun link => (link.source, link.target)

def addLink (kind : LinkKind) (source target : Name) : CoreM Unit :=
  modifyEnv (linksExt.addEntry · { kind, source, target })

def witnessName (headline : Name) : Name := headline.appendAfter "_applies"

def witnessType (headline : Expr) : MetaM Expr :=
  forallTelescope headline fun binders _ => binders.foldrM (init := mkConst ``True) fun binder body => do
    let type ← inferType binder
    return mkApp2 (.const ``Exists [← getLevel type]) type (← mkLambdaFVars #[binder] body)

def deriveWitness (headline : Name) (ref : Syntax) : CoreM Unit := do
  let name := witnessName headline
  let env := (← getEnv).setExporting false
  unless (env.getModuleIdxFor? headline).isNone && !env.contains name do return
  let some found := env.findAsync? headline | return
  unless found.kind matches .thm do return
  let signature := found.sig.get
  let (type, value) ← withoutExporting <| MetaM.run' do
    let type ← witnessType signature.type
    return (type, ← mkSorry type false)
  let used := (collectLevelParams {} type).params
  addDecl (.thmDecl { name, levelParams := signature.levelParams.filter used.contains, type, value })
  addDeclarationRangesFromSyntax name ref
  addLink .witness name headline

syntax (name := kills) "kills " ident : attr

syntax (name := terminates) "terminates " ident : attr

syntax (name := consistent) "consistent" : attr

syntax (name := tests) "tests " ident : attr

def linking (name : Name) (kind : LinkKind) (descr : String) : IO Unit :=
  registerBuiltinAttribute { name, descr, add := fun declaration stx _ => do
    let target ← if kind == .consistent then pure declaration
      else withoutExporting (realizeGlobalConstNoOverloadWithInfo stx[1])
    addLink kind declaration target
    if kind == .kills then deriveWitness target stx }

initialize linking `kills .kills "marks a kill of the headline it names and derives the headline's witness"

initialize linking `terminates .terminates "marks a headline as stating that the partial_fixpoint hole it names returns"

initialize linking `consistent .consistent "marks the theorem that the world claims hold together"

initialize linking `tests .tests "marks an IO test of the world claim it names"

def sourceOf (module : Name) : String := "/".intercalate (module.components.map toString) ++ ".lean"

syntax (name := testsMain) "SoftwareChallenge.testsMain" : term

@[term_elab testsMain] def elabTestsMain : TermElab := fun _ expectedType? => do
  let env ← getEnv
  let tests ← (links env .tests).mapM fun (test, claim) => do
    let module := ((env.getModuleIdxFor? test).map (env.header.moduleNames[·.toNat]!)).getD env.mainModule
    let line := ((← findDeclarationRanges? test).map (·.range.pos.line)).getD 0
    `(($(quote s!"{sourceOf module}:{line}"), $(quote test.toString), $(quote claim.toString), $(mkCIdent test)))
  elabTerm (← `(SoftwareChallenge.runTests #[$tests,*])) expectedType?

end SoftwareChallenge

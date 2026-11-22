module

public meta import Lean
public import SoftwareChallenge.Tests

public section
meta section

open Lean Elab Term

namespace SoftwareChallenge

inductive LinkKind where
  | kills | witness | terminates | consistent | tests
  deriving BEq

structure Link where
  kind : LinkKind
  source : Name
  target : Name
  line : Nat

initialize linksExt : SimplePersistentEnvExtension Link (Array Link) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

def links (env : Environment) (kind : LinkKind) : Array (Name × Name) :=
  ((linksExt.getState env).filter (·.kind == kind)).map fun link => (link.source, link.target)

syntax (name := kills) "kills " ident : attr

syntax (name := witness) "witness " ident : attr

syntax (name := terminates) "terminates " ident : attr

syntax (name := consistent) "consistent" : attr

syntax (name := tests) "tests " ident : attr

def linking (name : Name) (kind : LinkKind) (descr : String) : IO Unit :=
  registerBuiltinAttribute { name, descr, add := fun declaration stx _ => do
    let target ← if kind == .consistent then pure declaration
      else withoutExporting (realizeGlobalConstNoOverloadWithInfo stx[1])
    let line := ((← getFileMap).toPosition (stx.getPos?.getD 0)).line
    modifyEnv (linksExt.addEntry · { kind, source := declaration, target, line }) }

initialize linking `kills .kills "marks a kill of the headline it names"

initialize linking `witness .witness "marks a witness of the headline it names"

initialize linking `terminates .terminates "marks a headline as stating that the partial_fixpoint hole it names returns"

initialize linking `consistent .consistent "marks the theorem that the world claims hold together"

initialize linking `tests .tests "marks an IO test of the world claim it names"

def sourceOf (module : Name) : String := "/".intercalate (module.components.map toString) ++ ".lean"

syntax (name := testsMain) "SoftwareChallenge.testsMain" : term

@[term_elab testsMain] def elabTestsMain : TermElab := fun _ expectedType? => do
  let env ← getEnv
  let tests ← ((linksExt.getState env).filter (·.kind == .tests)).mapM fun link => do
    let module := ((env.getModuleIdxFor? link.source).map (env.header.moduleNames[·.toNat]!)).getD env.mainModule
    `(($(quote s!"{sourceOf module}:{link.line}"), $(quote link.source.toString), $(quote link.target.toString),
      $(mkCIdent link.source)))
  elabTerm (← `(SoftwareChallenge.runTests #[$tests,*])) expectedType?

end SoftwareChallenge

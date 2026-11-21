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
  line : Nat := 0

initialize linksExt : SimplePersistentEnvExtension Link (Array Link) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

def links (env : Environment) (kind : LinkKind) : Array (Name × Name) :=
  ((linksExt.getState env).filter (·.kind == kind)).map fun link => (link.source, link.target)

def addLink (kind : LinkKind) (source target : Name) (line : Nat := 0) : CoreM Unit :=
  modifyEnv (linksExt.addEntry · { kind, source, target, line })

def witnessName (headline : Name) : Name := headline.appendAfter "_applies"

def packageOf (env : Environment) (name : Name) : Option PkgId :=
  ((env.getModuleIdxFor? name).map env.getModulePackageByIdx?).getD env.getModulePackage?

initialize writtenNames : IO.Ref (NameMap NameSet) ← IO.mkRef {}

def writtenIn (module : Name) : IO NameSet := do
  if let some names := (← writtenNames.get).find? module then return names
  let olean ← findOLean module
  let (main, _) ← readModuleData olean
  let parts ← if main.isModule then (·.map (·.1)) <$> readModuleDataParts #[olean, OLeanLevel.server.adjustFileName olean]
    else pure #[main]
  let entries : Array EnvExtensionEntry :=
    ((parts.back?.bind (·.entries.find? (·.1 == declRangeExt.name))).map (·.2)).getD #[]
  let ranges : Array (Name × DeclarationRanges) := unsafe unsafeCast entries
  let names := ranges.foldl (init := {}) fun names (name, declared) =>
    if declared.range != declared.selectionRange then names.insert name else names
  writtenNames.modify (·.insert module names)
  return names

def isWritten (name : Name) : CoreM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? name with
  | some index => return (← writtenIn env.header.moduleNames[index.toNat]!).contains name
  | none => return (← findDeclarationRangesCore? name).any fun ranges => ranges.range != ranges.selectionRange

partial def witnessType (package : Option PkgId) (headline : Expr) : MetaM (Expr × Option Name) :=
  forallTelescope headline fun binders conclusion => do
    let env ← getEnv
    let (body, hidden) ← match conclusion with
      | .letE _ _ value scope _ => witnessType package (scope.instantiate1 value)
      | .app (.app (.const ``And _) left) right => do
        let (left, hidden) ← witnessType package left
        let (right, also) ← witnessType package right
        pure (if left.isConstOf ``True then right else if right.isConstOf ``True then left else mkAnd left right,
          hidden <|> also)
      | .app (.app (.const ``Exists _) type) (.lam name _ property _) =>
        witnessType package (.forallE name type property .default)
      | _ => do
        let head ← conclusion.getAppFn.constName?.filterM fun head =>
          if packageOf env head == package && wasOriginallyDefn env head then isWritten head else pure false
        match ← delta? conclusion fun name => head == some name && env.hasExposedBody name with
        | some unfolded => witnessType package unfolded
        | none => pure (mkConst ``True, head)
    let negated ← match binders.back? with
      | some last => pure (conclusion.isConstOf ``False && (← isProp (← inferType last)))
      | none => pure false
    let witness ← (if negated then binders.pop else binders).foldrM (init := body) fun binder body => do
      let type ← inferType binder
      return mkApp2 (.const ``Exists [← getLevel type]) type (← mkLambdaFVars #[binder] body)
    return (witness, hidden)

def deriveWitness (headline : Name) (ref : Syntax) : CoreM Unit := do
  let name := witnessName headline
  let env := (← getEnv).setExporting false
  unless (env.getModuleIdxFor? headline).isNone && !env.contains name do return
  let some found := env.findAsync? headline | return
  unless found.kind matches .thm do return
  let signature := found.sig.get
  let (type, value) ← withoutExporting <| MetaM.run' do
    let (type, _) ← witnessType (packageOf env headline) signature.type
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
    addLink kind declaration target ((← getFileMap).toPosition (stx.getPos?.getD 0)).line
    if kind == .kills then deriveWitness target stx }

initialize linking `kills .kills "marks a kill of the headline it names and derives the headline's witness"

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

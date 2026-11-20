module

public import SoftwareChallenge.CoreSpec.Role

@[expose] public section

namespace SoftwareChallenge

open Lean

structure ImportFact where
  name : Name
  comptime : Bool
  line : Nat
  deriving DecidableEq, Repr, Inhabited

structure ModuleFact where
  name : Name
  file : String
  usesModuleSystem : Bool
  imports : Array ImportFact
  deriving Repr

structure DeclarationFact where
  name : Name
  module : Name
  line : Nat
  computational : Bool
  isUnsafe : Bool
  isPartial : Bool
  external : Bool
  unfoldable : Bool
  replaced : Bool
  initializes : Bool
  effects : Bool
  debug : Bool
  axioms : Array Name
  written : Bool := true
  copyOf : Option Name := none
  copyOfInstanceMethod : Bool := false
  copyOfTotal : Bool := false
  copyOfFixpoint : Bool := false
  copyOfTerminated : Bool := false
  readsTag : Bool := false
  indexOf : Option Name := none
  indexedConstructors : Nat := 0
  indexedBuiltin : Bool := false
  implementationTyped : Bool := false
  implementationReadsTag : Bool := false
  deriving Repr

def DeclarationFact.compilerCopy (fact : DeclarationFact) : Bool :=
  !fact.written && fact.copyOf.isSome &&
    (fact.copyOfInstanceMethod || fact.copyOfTotal || fact.copyOfFixpoint && fact.copyOfTerminated)

def DeclarationFact.countsAsPartial (fact : DeclarationFact) : Bool :=
  fact.isPartial && !fact.compilerCopy

def DeclarationFact.generatedTagRead (fact : DeclarationFact) : Bool :=
  !fact.written && fact.readsTag

def DeclarationFact.generatedConstructorIndex (fact : DeclarationFact) : Bool :=
  !fact.written && fact.indexOf.isSome && fact.indexedConstructors != 1 && !fact.indexedBuiltin &&
    fact.implementationTyped && fact.implementationReadsTag

def DeclarationFact.countsAsUnsafe (fact : DeclarationFact) : Bool :=
  fact.isUnsafe && !fact.generatedTagRead

def DeclarationFact.countsAsReplaced (fact : DeclarationFact) : Bool :=
  fact.replaced && !fact.generatedConstructorIndex

def DeclarationFact.derivedPartial (fact : DeclarationFact) : Bool :=
  fact.isPartial && fact.copyOfInstanceMethod && !fact.copyOfTotal

structure Inventory where
  modules : Array ModuleFact
  declarations : Array DeclarationFact
  deriving Repr, Inhabited

def Inventory.RuntimeImport (inventory : Inventory) (source target : Name) : Prop :=
  ∃ fact ∈ inventory.modules, fact.name = source ∧
    ∃ dependency ∈ fact.imports, dependency.name = target ∧ dependency.comptime = false

structure Project where
  modules : Array (Name × Role)

def Project.role? (project : Project) (name : Name) : Option Role :=
  (project.modules.find? (·.1 == name)).map (·.2)

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

inductive Reason where
  | «unsafe» | «partial» | extern | implementedBy | initializer | io | debug | unfoldableExtern
  deriving DecidableEq, Repr

inductive Violation where
  | unplaced (module : Name)
  | legacy (module : Name)
  | forbiddenImport (module dependency : Name) (role : Role)
  | axioms (declaration : Name) (found : Array Name)
  | impure (declaration : Name) (role : Role) (reasons : List Reason)
  deriving DecidableEq, Repr

def DeclarationFact.Allowed (fact : DeclarationFact) : Role → Prop
  | .coreSpec | .coreCode =>
    fact.countsAsUnsafe = false ∧ fact.countsAsPartial = false ∧ fact.external = false ∧
      fact.countsAsReplaced = false ∧ fact.initializes = false ∧ fact.effects = false ∧ fact.debug = false
  | .worldSpec =>
    fact.countsAsUnsafe = false ∧ fact.countsAsPartial = false ∧ fact.countsAsReplaced = false ∧
      fact.initializes = false ∧ fact.debug = false ∧ (fact.external = true → fact.unfoldable = false) ∧
      (fact.external = false → fact.effects = false)
  | .worldCode => fact.countsAsUnsafe = false ∧ fact.external = false ∧ fact.countsAsReplaced = false
  | .tooling => True

structure Project.Admits (project : Project) (inventory : Inventory) : Prop where
  placed : ∀ fact ∈ inventory.modules, ∃ role, project.role? fact.name = some role
  modular : ∀ fact ∈ inventory.modules, fact.usesModuleSystem = true
  layered : ∀ fact ∈ inventory.modules, ∀ dependency ∈ fact.imports, dependency.comptime = false →
    ∀ source target, project.role? fact.name = some source → project.role? dependency.name = some target →
      source.MayImport target
  pure : ∀ fact ∈ inventory.declarations, ∃ role, project.role? fact.module = some role ∧
    (∀ used ∈ fact.axioms, used ∈ standardAxioms) ∧ (fact.computational = true → fact.Allowed role)

end SoftwareChallenge

module

public import Lean.Data.Name

public section

open Lean

namespace SoftwareChallenge

inductive Role where
  | coreSpec | worldSpec | coreCode | worldCode | tooling
  deriving DecidableEq, Repr

instance : ToString Role where
  toString
    | .coreSpec => "CoreSpec"
    | .worldSpec => "WorldSpec"
    | .coreCode => "CoreCode"
    | .worldCode => "WorldCode"
    | .tooling => "tooling"

def Role.Inner (role : Role) : Prop :=
  role = .coreSpec ∨ role = .worldSpec ∨ role = .coreCode

def Role.ofName (name : Name) : Role :=
  (name.components.findSome? fun component =>
    [Role.coreSpec, .worldSpec, .coreCode, .worldCode].find? (toString · == component.toString)).getD .tooling

structure Project where
  modules : Array (Name × Role)
  executable : Bool := false

def Project.ofPackage (modules : Array Name) (executable : Bool) : Project :=
  { modules := modules.map fun name => (name, Role.ofName name), executable }

def Project.role? (project : Project) (name : Name) : Option Role :=
  (project.modules.find? (·.1 == name)).map (·.2)

structure ImportFact where
  name : Name
  comptime : Bool

structure ModuleFact where
  name : Name
  usesModuleSystem : Bool
  imports : Array ImportFact

structure DeclarationFact where
  name : Name
  moduleName : Name
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

structure Inventory where
  modules : Array ModuleFact
  declarations : Array DeclarationFact

def Inventory.RuntimeImport (inventory : Inventory) (source target : Name) : Prop :=
  ∃ fact ∈ inventory.modules, fact.name = source ∧
    ∃ dependency ∈ fact.imports, dependency.name = target ∧ dependency.comptime = false

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def Role.permits : Role → Role → Bool
  | .tooling, _ => true
  | .worldCode, target => target != .tooling
  | .worldSpec, target => target == .coreSpec || target == .worldSpec
  | .coreCode, target => target == .coreSpec || target == .coreCode
  | .coreSpec, target => target == .coreSpec

def Project.admits (project : Project) (source : Role) (dependency : ImportFact) : Bool :=
  dependency.comptime || match project.role? dependency.name with
    | some target => source.permits target
    | none => true

def Project.moduleAdmitted (project : Project) (fact : ModuleFact) : Bool :=
  match project.role? fact.name with
  | some role => fact.usesModuleSystem && fact.imports.all (project.admits role)
  | none => false

def DeclarationFact.reasons (role : Role) (fact : DeclarationFact) : List String :=
  let flags := [(fact.isUnsafe, "unsafe"), (fact.isPartial, "partial"),
    (fact.external, "@[extern]"), (fact.replaced, "@[implemented_by]"),
    (fact.initializes, "initializer"), (fact.effects, "IO"), (fact.debug, "dbg builtin")]
  let raised := fun (allowed : List String) =>
    flags.filterMap fun (set, reason) => if set && !allowed.contains reason then some reason else none
  if !fact.computational then [] else match role with
    | .coreSpec | .coreCode => raised []
    | .worldSpec =>
      if !fact.external then raised []
      else if fact.unfoldable then ["@[extern] with a body the kernel unfolds"]
      else raised ["@[extern]", "IO"]
    | .worldCode => raised ["partial", "initializer", "IO", "dbg builtin"]
    | .tooling => []

def Project.check (project : Project) (inventory : Inventory) : Bool :=
  inventory.modules.all project.moduleAdmitted &&
    inventory.declarations.all fun fact => match project.role? fact.moduleName with
      | some role => fact.axioms.isEmpty && (fact.reasons role).isEmpty
      | none => false

private theorem permits_inner {source target : Role} (permitted : source.permits target = true)
    (inner : source.Inner) : target.Inner := by
  cases source <;> cases target <;> simp_all [Role.Inner, Role.permits]

private theorem import_step {project : Project} {inventory : Inventory}
    (accepted : project.check inventory = true) {source target : Name}
    (inner : ∀ role, project.role? source = some role → role.Inner)
    (edge : inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  obtain ⟨fact, member, rfl, dependency, imported, rfl, runtime⟩ := edge
  simp only [Project.check, Bool.and_eq_true, Array.all_eq_true'] at accepted
  have admitted := accepted.1 fact member
  unfold Project.moduleAdmitted at admitted
  intro reached found
  cases owner : project.role? fact.name with
  | none => simp [owner] at admitted
  | some role =>
    simp only [owner, Bool.and_eq_true, Array.all_eq_true'] at admitted
    have permitted := admitted.2 dependency imported
    simp only [Project.admits, runtime, Bool.false_or, found] at permitted
    exact permits_inner permitted (inner role owner)

theorem layering_sound (project : Project) (inventory : Inventory)
    (accepted : project.check inventory = true) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  induction reaches with
  | single edge => exact import_step accepted (fun _ owner => by simp_all) edge
  | tail _ edge previous => exact import_step accepted previous edge

end SoftwareChallenge

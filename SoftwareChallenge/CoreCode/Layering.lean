module

public import SoftwareChallenge.CoreSpec.Package

public section

namespace SoftwareChallenge

open Lean

def Project.ofPackage (modules : Array Name) : Project :=
  { modules := modules.map fun name => (name, Role.ofName name) }

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

def DeclarationFact.reasons (role : Role) (fact : DeclarationFact) : List Reason :=
  let flags := [(fact.isUnsafe, Reason.«unsafe»), (fact.isPartial, .«partial»), (fact.external, .extern),
    (fact.replaced, .implementedBy), (fact.initializes, .initializer), (fact.effects, .io), (fact.debug, .debug)]
  let raised := fun (allowed : List Reason) =>
    flags.filterMap fun (set, reason) => if set && !allowed.contains reason then some reason else none
  if !fact.computational then [] else match role with
    | .coreSpec | .coreCode => raised []
    | .worldSpec =>
      if !fact.external then raised []
      else if fact.unfoldable then [.unfoldableExtern]
      else raised [.extern, .io]
    | .worldCode => raised [.«partial», .initializer, .io, .debug]
    | .tooling => []

def DeclarationFact.nonstandardAxioms (fact : DeclarationFact) : Array Name :=
  fact.axioms.filter (!standardAxioms.contains ·)

def Project.check (project : Project) (inventory : Inventory) : Bool :=
  inventory.modules.all project.moduleAdmitted &&
    inventory.declarations.all fun fact => match project.role? fact.module with
      | some role => fact.nonstandardAxioms.isEmpty && (fact.reasons role).isEmpty
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

theorem Project.check_layered (project : Project) (inventory : Inventory)
    (accepted : project.check inventory = true) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  induction reaches with
  | single edge => exact import_step accepted (fun _ owner => by simp_all) edge
  | tail _ edge previous => exact import_step accepted previous edge

end SoftwareChallenge

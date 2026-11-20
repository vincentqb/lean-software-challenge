module

public import SoftwareChallenge.CoreSpec.Package

public section

namespace SoftwareChallenge

open Lean

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

def DeclarationFact.reasons (role : Role) (fact : DeclarationFact) : List Reason :=
  let flags := [(fact.isUnsafe, Reason.«unsafe»), (fact.countsAsPartial, .«partial»), (fact.external, .extern),
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

def ModuleFact.violations (project : Project) (fact : ModuleFact) : Array Violation :=
  match project.role? fact.name with
  | none => #[.unplaced fact.name]
  | some role =>
    (if fact.usesModuleSystem then #[] else #[.legacy fact.name]) ++
      (fact.imports.filter (!project.admits role ·)).map fun dependency =>
        .forbiddenImport fact.name dependency.name role

def DeclarationFact.violations (project : Project) (fact : DeclarationFact) : Array Violation :=
  match project.role? fact.module with
  | none => #[.unplaced fact.module]
  | some role =>
    let found := fact.axioms.filter (!standardAxioms.contains ·)
    let reasons := fact.reasons role
    (if found.isEmpty then #[] else #[.axioms fact.name found]) ++
      if reasons.isEmpty then #[] else #[.impure fact.name role reasons]

def Project.violations (project : Project) (inventory : Inventory) : Array Violation :=
  inventory.modules.flatMap (·.violations project) ++ inventory.declarations.flatMap (·.violations project)

theorem Role.permits_inner {source target : Role} (permitted : source.permits target = true)
    (inner : source.Inner) : target.Inner := by
  cases source <;> cases target <;> simp_all [Role.Inner, Role.permits]

theorem DeclarationFact.reasons_eq_nil_iff_allowed {role : Role} {fact : DeclarationFact} :
    fact.reasons role = [] ↔ (fact.computational = true → fact.Allowed role) := by
  unfold DeclarationFact.reasons DeclarationFact.Allowed
  cases fact.computational <;> cases role <;> cases fact.external <;> cases fact.unfoldable <;>
    simp [List.filterMap_eq_nil_iff, and_comm]

theorem ModuleFact.violations_eq_empty_iff {project : Project} {fact : ModuleFact} :
    fact.violations project = #[] ↔ ∃ role, project.role? fact.name = some role ∧
      fact.usesModuleSystem = true ∧ ∀ dependency ∈ fact.imports, project.admits role dependency = true := by
  unfold ModuleFact.violations
  cases project.role? fact.name <;> cases fact.usesModuleSystem <;> simp [Array.filter_eq_empty_iff]

theorem DeclarationFact.violations_eq_empty_iff {project : Project} {fact : DeclarationFact} :
    fact.violations project = #[] ↔ ∃ role, project.role? fact.module = some role ∧
      (∀ used ∈ fact.axioms, used ∈ standardAxioms) ∧ fact.reasons role = [] := by
  unfold DeclarationFact.violations
  cases project.role? fact.module <;> simp [Array.filter_eq_empty_iff]

theorem Project.violations_eq_empty_iff {project : Project} {inventory : Inventory} :
    project.violations inventory = #[] ↔ (∀ fact ∈ inventory.modules, fact.violations project = #[]) ∧
      ∀ fact ∈ inventory.declarations, fact.violations project = #[] := by
  simp [Project.violations]

theorem Project.import_step {project : Project} {inventory : Inventory}
    (accepted : project.violations inventory = #[]) {source target : Name}
    (inner : ∀ role, project.role? source = some role → role.Inner)
    (edge : inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  obtain ⟨fact, member, rfl, dependency, imported, rfl, runtime⟩ := edge
  obtain ⟨role, classified, -, admitted⟩ :=
    ModuleFact.violations_eq_empty_iff.mp ((Project.violations_eq_empty_iff.mp accepted).1 fact member)
  intro reached found
  have permitted := admitted dependency imported
  simp only [Project.admits, runtime, Bool.false_or, found] at permitted
  exact Role.permits_inner permitted (inner role classified)

end SoftwareChallenge

module

public import SoftwareChallenge.CoreCode.Layering
import all SoftwareChallenge.CoreCode.Layering

public section

namespace SoftwareChallenge

open Lean

theorem layering_sound (project : Project) (inventory : Inventory)
    (accepted : project.violations inventory = #[]) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  induction reaches with
  | single edge => exact Project.import_step accepted (fun _ owner => by simp_all) edge
  | tail _ edge previous => exact Project.import_step accepted previous edge

theorem layering_sound_rejects_accepting :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => (#[] : Array Violation)) project inventory = #[] →
      ∀ (source target : Name) (role : Role), project.role? source = some role → role.Inner →
      Relation.TransGen inventory.RuntimeImport source target →
      ∀ reached, project.role? target = some reached → reached.Inner := by
  intro sound
  have escaped := sound { modules := #[(`A, .coreCode), (`W, .worldCode)] }
    { modules := #[{ name := `A, file := "A.lean", usesModuleSystem := true,
                     imports := #[{ name := `W, comptime := false, line := 1 }] }]
      declarations := #[] }
    rfl `A `W .coreCode (by simp [Project.role?]) (by simp [Role.Inner])
    (.single (by simp [Inventory.RuntimeImport])) .worldCode (by simp [Project.role?])
  simp [Role.Inner] at escaped

theorem layering_sound_applies :
    ∃ (project : Project) (inventory : Inventory) (source target : Name) (role reached : Role),
      project.violations inventory = #[] ∧ project.role? source = some role ∧ role.Inner ∧
        Relation.TransGen inventory.RuntimeImport source target ∧ project.role? target = some reached :=
  ⟨{ modules := #[(`A, .coreCode), (`B, .coreSpec)] },
    { modules := #[{ name := `A, file := "A.lean", usesModuleSystem := true,
                     imports := #[{ name := `B, comptime := false, line := 1 }] }]
      declarations := #[] },
    `A, `B, .coreCode, .coreSpec,
    by simp [Project.violations, ModuleFact.violations, Project.role?, Project.admits, Role.permits],
    by simp [Project.role?], by simp [Role.Inner],
    .single (by simp [Inventory.RuntimeImport]), by simp [Project.role?]⟩

theorem purity_sound (project : Project) (inventory : Inventory)
    (accepted : project.violations inventory = #[]) (fact : DeclarationFact)
    (listed : fact ∈ inventory.declarations) :
    ∃ role, project.role? fact.module = some role ∧ (∀ used ∈ fact.axioms, used ∈ standardAxioms) ∧
      (fact.computational = true → fact.Allowed role) := by
  obtain ⟨role, classified, standard, clean⟩ :=
    DeclarationFact.violations_eq_empty_iff.mp ((Project.violations_eq_empty_iff.mp accepted).2 fact listed)
  exact ⟨role, classified, standard, DeclarationFact.reasons_eq_nil_iff_allowed.mp clean⟩

theorem purity_sound_rejects_accepting :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => (#[] : Array Violation)) project inventory = #[] →
      ∀ (fact : DeclarationFact), fact ∈ inventory.declarations →
      ∃ role, project.role? fact.module = some role ∧ (∀ used ∈ fact.axioms, used ∈ standardAxioms) ∧
        (fact.computational = true → fact.Allowed role) := by
  intro sound
  obtain ⟨role, classified, -, allowed⟩ := sound { modules := #[(`A, .coreCode)] }
    { modules := #[]
      declarations := #[{ name := `A.hidden, module := `A, line := 1, computational := true,
                          isUnsafe := true, isPartial := false, external := false, unfoldable := true,
                          replaced := false, initializes := false, effects := false, debug := false,
                          axioms := #[] }] }
    rfl _ (Array.mem_singleton.mpr rfl)
  simp [Project.role?] at classified
  subst classified
  simp [DeclarationFact.Allowed, DeclarationFact.countsAsUnsafe, DeclarationFact.generatedTagRead] at allowed

theorem purity_sound_applies :
    ∃ (project : Project) (inventory : Inventory) (fact : DeclarationFact),
      project.violations inventory = #[] ∧ fact ∈ inventory.declarations :=
  ⟨{ modules := #[(`A, .coreCode)] },
    { modules := #[]
      declarations := #[{ name := `A.pure, module := `A, line := 1, computational := true,
                          isUnsafe := false, isPartial := false, external := false, unfoldable := true,
                          replaced := false, initializes := false, effects := false, debug := false,
                          axioms := #[] }] },
    _, by simp [Project.violations, DeclarationFact.violations, DeclarationFact.reasons, DeclarationFact.countsAsUnsafe,
      DeclarationFact.countsAsPartial, DeclarationFact.countsAsReplaced, Project.role?],
    Array.mem_singleton.mpr rfl⟩

end SoftwareChallenge

module

public import SoftwareChallenge.CoreCode.Layering
import all SoftwareChallenge.CoreCode.Layering

public section

namespace SoftwareChallenge

open Lean

theorem Role.permits_iff_mayImport {source target : Role} :
    source.permits target = true ↔ source.MayImport target := by
  cases source <;> cases target <;> simp [Role.permits, Role.MayImport]

theorem Project.violations_eq_empty_iff_admits (project : Project) (inventory : Inventory) :
    project.violations inventory = #[] ↔ project.Admits inventory := by
  rw [Project.violations_eq_empty_iff]
  constructor
  · rintro ⟨modules, declarations⟩
    refine ⟨fun fact member => ?_, fun fact member => ?_, ?_, fun fact member => ?_⟩
    · obtain ⟨role, classified, -, -⟩ := ModuleFact.violations_eq_empty_iff.mp (modules fact member)
      exact ⟨role, classified⟩
    · obtain ⟨role, -, modular, -⟩ := ModuleFact.violations_eq_empty_iff.mp (modules fact member)
      exact modular
    · intro fact member dependency imported runtime source target classified found
      obtain ⟨role, owner, -, admitted⟩ := ModuleFact.violations_eq_empty_iff.mp (modules fact member)
      have permitted := admitted dependency imported
      simp only [Project.admits, runtime, Bool.false_or, found] at permitted
      rw [owner] at classified
      cases classified
      exact Role.permits_iff_mayImport.mp permitted
    · obtain ⟨role, owner, standard, reasons⟩ :=
        DeclarationFact.violations_eq_empty_iff.mp (declarations fact member)
      exact ⟨role, owner, standard, DeclarationFact.reasons_eq_nil_iff_allowed.mp reasons⟩
  · intro admits
    refine ⟨fun fact member => ModuleFact.violations_eq_empty_iff.mpr ?_,
      fun fact member => DeclarationFact.violations_eq_empty_iff.mpr ?_⟩
    · obtain ⟨role, owner⟩ := admits.placed fact member
      refine ⟨role, owner, admits.modular fact member, fun dependency imported => ?_⟩
      unfold Project.admits
      cases runtime : dependency.comptime
      · cases found : project.role? dependency.name with
        | none => simp
        | some target =>
          simpa using Role.permits_iff_mayImport.mpr
            (admits.layered fact member dependency imported runtime role target owner found)
      · simp
    · obtain ⟨role, owner, standard, allowed⟩ := admits.pure fact member
      exact ⟨role, owner, standard, DeclarationFact.reasons_eq_nil_iff_allowed.mpr allowed⟩

theorem Project.violations_eq_empty_iff_admits_rejects_accepting :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => (#[] : Array Violation)) project inventory = #[] ↔
        project.Admits inventory := by
  intro holds
  have admits := (holds { modules := #[] }
    { modules := #[{ name := `A, file := "A.lean", usesModuleSystem := true, imports := #[] }],
      declarations := #[] }).mp rfl
  obtain ⟨role, found⟩ := admits.placed { name := `A, file := "A.lean", usesModuleSystem := true, imports := #[] }
    (by simp)
  simp [Project.role?] at found

theorem Project.violations_eq_empty_iff_admits_rejects_refusing :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => #[Violation.unplaced .anonymous]) project inventory = #[] ↔
        project.Admits inventory := by
  intro holds
  have refused := (holds { modules := #[] } { modules := #[], declarations := #[] }).mpr
    ⟨by simp, by simp, by simp, by simp⟩
  simp at refused

end SoftwareChallenge

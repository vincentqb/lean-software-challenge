module

import all SoftwareChallenge.Policy
meta import SoftwareChallenge.Audit

namespace SoftwareChallengeTests.Policy

open Lean SoftwareChallenge

def layered : Project := { modules := #[(`A, .coreCode), (`B, .coreSpec), (`W, .worldCode)] }

def importing (target : Name) : Inventory :=
  { modules := #[{ name := `A, usesModuleSystem := true, imports := #[{ name := target, comptime := false }] }],
    declarations := #[] }

theorem layering_sound_witness :
    ∃ (project : Project) (inventory : Inventory) (source target : Name) (role reached : Role),
      project.check inventory = true ∧ project.role? source = some role ∧ role.Inner ∧
        Relation.TransGen inventory.RuntimeImport source target ∧ project.role? target = some reached :=
  ⟨layered, importing `B, `A, `B, .coreCode, .coreSpec,
    by simp [layered, importing, Project.check, Project.moduleAdmitted, Project.role?, Project.admits, Role.permits],
    by simp [layered, Project.role?], by simp [Role.Inner],
    .single (by simp [importing, Inventory.RuntimeImport]), by simp [layered, Project.role?]⟩

theorem layering_sound_rejects_accepting :
    ¬ ∀ (project : Project) (inventory : Inventory), (fun _ _ => true) project inventory = true →
      ∀ (source target : Name) (role : Role), project.role? source = some role → role.Inner →
        Relation.TransGen inventory.RuntimeImport source target →
          ∀ reached, project.role? target = some reached → reached.Inner := by
  intro sound
  have escaped := sound layered (importing `W) rfl `A `W .coreCode (by simp [layered, Project.role?])
    (by simp [Role.Inner]) (.single (by simp [importing, Inventory.RuntimeImport])) .worldCode
    (by simp [layered, Project.role?])
  simp [Role.Inner] at escaped

theorem witnesses?_sound_witness :
    ∃ (replaceable : Name → Bool) (pattern target : Shape) (σ : Witnesses),
      pattern.witnesses? replaceable target = some σ :=
  ⟨(· == `f), .const `f [], .natLit 0, [(`f, .natLit 0)],
    by simp [Shape.witnesses?, Shape.collect, Shape.subst, Witnesses.find?, Shape.closedUnder]⟩

theorem witnesses?_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses},
      (fun _ _ _ => (some [] : Option Witnesses)) replaceable pattern target = some σ →
        (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  intro sound
  have instantiates := (sound (replaceable := fun _ => false) (pattern := .natLit 0) (target := .natLit 1) rfl).2
  simp [Shape.subst] at instantiates

theorem witnesses?_complete_witness :
    ∃ (replaceable : Name → Bool) (pattern target : Shape) (σ : Witnesses),
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) ∧
        pattern.subst replaceable σ = target :=
  ⟨(· == `f), .const `f [], .natLit 0, [(`f, .natLit 0)], by simp [Shape.closedUnder],
    by simp [Shape.subst, Witnesses.find?]⟩

theorem witnesses?_complete_rejects_refusing :
    ¬ ∀ {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses},
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) →
        pattern.subst replaceable σ = target → ((fun _ _ _ => (none : Option Witnesses)) replaceable pattern target).isSome := by
  intro complete
  have found := complete (replaceable := fun _ => false) (pattern := .natLit 0) (σ := []) (by simp) rfl
  simp at found

theorem witnesses?_isSome_iff_witness :
    ∃ (replaceable : Name → Bool) (pattern target : Shape), (pattern.witnesses? replaceable target).isSome :=
  ⟨(· == `f), .const `f [], .natLit 0,
    by simp [Shape.witnesses?, Shape.collect, Shape.subst, Witnesses.find?, Shape.closedUnder]⟩

theorem witnesses?_isSome_iff_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {pattern target : Shape},
      ((fun _ _ _ => (some [] : Option Witnesses)) replaceable pattern target).isSome ↔
        ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  intro iff
  obtain ⟨σ, _, instantiates⟩ :=
    (iff (replaceable := fun _ => false) (pattern := .natLit 0) (target := .natLit 1)).mp rfl
  simp [Shape.subst] at instantiates

theorem independent_sound_witness :
    ∃ (replaceable : Name → Bool) (headline kill : Shape) (others : List Shape),
      Shape.independent replaceable headline others kill = true :=
  ⟨(· == `f), .const `f [], .app (.app (.const ``And []) (.app (.const ``Not []) (.natLit 0))) (.natLit 0),
    [.const `f []], by
      simp [Shape.independent, Shape.independence, Shape.conjunction, Shape.negation, Shape.witnesses?,
        Shape.collect, Shape.subst, Witnesses.find?, Shape.closedUnder]⟩

theorem independent_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape},
      (fun _ _ _ _ => true) replaceable headline others kill = true →
        others ≠ [] ∧ ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
          kill = Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) := by
  intro sound
  exact (sound (replaceable := fun _ => false) (headline := .natLit 0) (kill := .natLit 0) (others := []) rfl).1 rfl

theorem applies_sound_witness :
    ∃ (premises : List Shape) (inputs : List (Universe × Shape)) (preconditions : List Shape) (witness : Shape),
      Shape.applies premises inputs preconditions witness = true :=
  ⟨[], [], [.natLit 0], .natLit 0, by
    simp [Shape.applies, Shape.applicability, Shape.existential, Shape.conjunction, Shape.witnesses?,
      Shape.collect, Shape.subst]⟩

theorem applies_sound_rejects_accepting :
    ¬ ∀ {premises : List Shape} {inputs : List (Universe × Shape)} {preconditions : List Shape} {witness : Shape},
      (fun _ _ _ _ => true) premises inputs preconditions witness = true →
        preconditions ≠ [] ∧ witness = premises.foldr .forallE (Shape.existential inputs (Shape.conjunction preconditions)) := by
  intro sound
  exact (sound (premises := []) (inputs := []) (preconditions := []) (witness := .natLit 0) rfl).1 rfl

meta section

run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  for (statement, function, kill) in #[
      (``layering_sound, ``Project.check, ``layering_sound_rejects_accepting),
      (``Shape.witnesses?_sound, ``Shape.witnesses?, ``witnesses?_sound_rejects_accepting),
      (``Shape.witnesses?_complete, ``Shape.witnesses?, ``witnesses?_complete_rejects_refusing),
      (``Shape.witnesses?_isSome_iff, ``Shape.witnesses?, ``witnesses?_isSome_iff_rejects_accepting),
      (``Shape.independent_sound, ``Shape.independent, ``independent_sound_rejects_accepting),
      (``Shape.applies_sound, ``Shape.applies, ``applies_sound_rejects_accepting)] do
    unless Audit.kills env (NameSet.empty.insert function) statement kill do
      throwError "{kill} is not `¬` {statement} with {function} replaced"
  for (statement, witness) in #[(``layering_sound, ``layering_sound_witness),
      (``Shape.witnesses?_sound, ``witnesses?_sound_witness),
      (``Shape.witnesses?_complete, ``witnesses?_complete_witness),
      (``Shape.independent_sound, ``independent_sound_witness),
      (``Shape.applies_sound, ``applies_sound_witness)] do
    let some preconditions ← Audit.preconditionsOf { modules := #[] } {} statement (← getConstInfo statement).type
      | throwError "{statement} has no precondition"
    unless preconditions.witnessedBy (← getConstInfo witness).type do
      throwError "{witness} is not `{preconditions.expected}`"

end

end SoftwareChallengeTests.Policy

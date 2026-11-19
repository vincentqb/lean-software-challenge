module

public import SoftwareChallenge.CoreCode.Match

public section

namespace SoftwareChallenge

open Lean

theorem Shape.witnesses?_sound {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (found : pattern.witnesses? replaceable target = some σ) :
    (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target :=
  Shape.witnesses?_some found

theorem Shape.witnesses?_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses},
      (fun (_ : Name → Bool) (_ _ : Shape) => (some [] : Option Witnesses)) replaceable pattern target = some σ →
      (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  intro sound
  have instantiates := (sound (replaceable := fun _ => false) (pattern := .natLit 0) (target := .natLit 1) rfl).2
  simp [Shape.subst] at instantiates

theorem Shape.witnesses?_complete {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true)
    (instantiates : pattern.subst replaceable σ = target) :
    (pattern.witnesses? replaceable target).isSome :=
  Shape.witnesses?_isSome_of_subst closed instantiates

theorem Shape.witnesses?_complete_rejects_refusing :
    ¬ ∀ {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses},
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) →
      pattern.subst replaceable σ = target →
      ((fun (_ : Name → Bool) (_ _ : Shape) => (none : Option Witnesses)) replaceable pattern target).isSome := by
  intro complete
  have found := complete (replaceable := fun _ => false) (pattern := .natLit 0) (σ := []) (by simp) rfl
  simp at found

theorem Shape.witnesses?_sound_applies :
    ∃ (replaceable : Name → Bool) (pattern target : Shape) (σ : Witnesses),
      pattern.witnesses? replaceable target = some σ := by
  obtain ⟨σ, found⟩ := Option.isSome_iff_exists.mp
    (Shape.witnesses?_complete (replaceable := fun _ => false) (pattern := .natLit 0) (σ := []) (by simp) rfl)
  exact ⟨_, _, _, σ, found⟩

theorem Shape.isKill_sound {replaceable : Name → Bool} {headline kill : Shape}
    (accepted : headline.isKill replaceable kill = true) :
    ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
      kill = (headline.subst replaceable σ).negation := by
  obtain ⟨rejected, rfl, found⟩ := Shape.isKill_eq_true.mp accepted
  obtain ⟨σ, found⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨closed, instantiates⟩ := Shape.witnesses?_sound found
  exact ⟨σ, closed, by rw [instantiates]⟩

theorem Shape.isKill_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {headline kill : Shape},
      (fun (_ : Name → Bool) (_ _ : Shape) => true) replaceable headline kill = true →
      ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
        kill = (headline.subst replaceable σ).negation := by
  intro sound
  obtain ⟨σ, _, negated⟩ := sound (replaceable := fun _ => false) (headline := .natLit 0) (kill := .natLit 0) rfl
  simp [Shape.subst, Shape.negation] at negated

theorem Shape.isKill_complete {replaceable : Name → Bool} {headline : Shape} {σ : Witnesses}
    (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) :
    headline.isKill replaceable (headline.subst replaceable σ).negation = true :=
  Shape.isKill_eq_true.mpr ⟨_, rfl, Shape.witnesses?_complete closed rfl⟩

theorem Shape.isKill_complete_rejects_refusing :
    ¬ ∀ {replaceable : Name → Bool} {headline : Shape} {σ : Witnesses},
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) →
      (fun (_ : Name → Bool) (_ _ : Shape) => false) replaceable headline
        (headline.subst replaceable σ).negation = true := by
  intro complete
  have accepted := complete (replaceable := fun _ => false) (headline := .natLit 0) (σ := []) (by simp)
  simp at accepted

theorem Shape.isKill_sound_applies :
    ∃ (replaceable : Name → Bool) (headline kill : Shape), headline.isKill replaceable kill = true :=
  ⟨fun _ => false, .natLit 0, _, Shape.isKill_complete (σ := []) (by simp)⟩

theorem Shape.independent_sound {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape}
    (accepted : headline.independent replaceable others kill = true) :
    others ≠ [] ∧ ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
      kill = Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) := by
  obtain ⟨fixed, nonempty, found⟩ := Shape.independent_eq_true.mp accepted
  obtain ⟨σ, found⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨closed, instantiates⟩ := Shape.witnesses?_sound found
  exact ⟨nonempty, σ, closed, by rw [← instantiates, Shape.subst_independence fixed]⟩

theorem Shape.independent_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape},
      (fun (_ : Name → Bool) (_ : Shape) (_ : List Shape) (_ : Shape) => true) replaceable headline others kill = true →
      others ≠ [] ∧ ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
        kill = Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) := by
  intro sound
  exact (sound (replaceable := fun _ => false) (headline := .natLit 0) (kill := .natLit 0) (others := []) rfl).1 rfl

theorem Shape.independent_complete {replaceable : Name → Bool} {headline : Shape} {others : List Shape}
    {σ : Witnesses} (fixed : replaceable ``And = false ∧ replaceable ``Not = false ∧ replaceable ``True = false)
    (nonempty : others ≠ []) (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) :
    headline.independent replaceable others
      (Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ))) = true :=
  Shape.independent_eq_true.mpr
    ⟨fixed, nonempty, Shape.witnesses?_complete closed (Shape.subst_independence fixed)⟩

theorem Shape.independent_complete_rejects_refusing :
    ¬ ∀ {replaceable : Name → Bool} {headline : Shape} {others : List Shape} {σ : Witnesses},
      (replaceable ``And = false ∧ replaceable ``Not = false ∧ replaceable ``True = false) → others ≠ [] →
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) →
      (fun (_ : Name → Bool) (_ : Shape) (_ : List Shape) (_ : Shape) => false) replaceable headline others
        (Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ))) = true := by
  intro complete
  have accepted := complete (replaceable := fun _ => false) (headline := .natLit 0) (others := [.natLit 0])
    (σ := []) ⟨rfl, rfl, rfl⟩ (by simp) (by simp)
  simp at accepted

theorem Shape.independent_sound_applies :
    ∃ (replaceable : Name → Bool) (headline kill : Shape) (others : List Shape),
      headline.independent replaceable others kill = true :=
  ⟨fun _ => false, .natLit 0, _, [.natLit 0], Shape.independent_complete ⟨rfl, rfl, rfl⟩ (by simp) (σ := []) (by simp)⟩

end SoftwareChallenge

module

public import SoftwareChallenge.CoreSpec.Shape

public section

namespace SoftwareChallenge

open Lean

namespace Shape

def collect (replaceable : Name → Bool) : Shape → Shape → Witnesses → Witnesses
  | .const name levels, target, σ =>
    if replaceable name ∧ σ.find? name = none ∧ target ≠ .const name levels then (name, target) :: σ else σ
  | .app f a, .app g b, σ => collect replaceable a b (collect replaceable f g σ)
  | .lam t b, .lam u c, σ | .forallE t b, .forallE u c, σ =>
    collect replaceable b c (collect replaceable t u σ)
  | .letE t v b, .letE u w c, σ =>
    collect replaceable b c (collect replaceable v w (collect replaceable t u σ))
  | .proj _ _ v, .proj _ _ w, σ => collect replaceable v w σ
  | _, _, σ => σ

def witnesses? (replaceable : Name → Bool) (pattern target : Shape) : Option Witnesses :=
  let σ := collect replaceable pattern target []
  if σ.all (·.2.closedUnder 0) ∧ pattern.subst replaceable σ = target then some σ else none

private theorem find?_mem {σ : Witnesses} {name : Name} {witness : Shape}
    (found : σ.find? name = some witness) : (name, witness) ∈ σ := by
  induction σ with
  | nil => simp [Witnesses.find?] at found
  | cons entry rest ih =>
    obtain ⟨key, w⟩ := entry
    by_cases same : key = name
    · subst same; simp_all [Witnesses.find?]
    · simp only [Witnesses.find?, same, ite_false] at found
      exact List.mem_cons_of_mem _ (ih found)

private theorem collect_extends {replaceable : Name → Bool} {σ' : Witnesses} {pattern : Shape}
    {σ : Witnesses} {name : Name} {witness : Shape} (found : σ.find? name = some witness) :
    (collect replaceable pattern (pattern.subst replaceable σ') σ).find? name = some witness := by
  induction pattern generalizing σ with
  | const key levels =>
    simp only [collect]
    split
    · rename_i h
      have : key ≠ name := fun same => by simp_all
      simp [Witnesses.find?, this, found]
    · exact found
  | app f a ihf iha => exact iha (ihf found)
  | lam t b iht ihb => exact ihb (iht found)
  | forallE t b iht ihb => exact ihb (iht found)
  | letE t v b iht ihv ihb => exact ihb (ihv (iht found))
  | proj _ _ v ih => exact ih found
  | _ => simpa [collect, subst] using found

private theorem collect_from {replaceable : Name → Bool} {σ' : Witnesses} {pattern : Shape}
    {σ : Witnesses} {entry : Name × Shape}
    (member : entry ∈ collect replaceable pattern (pattern.subst replaceable σ') σ) :
    entry ∈ σ ∨ replaceable entry.1 = true ∧ σ'.find? entry.1 = some entry.2 := by
  induction pattern generalizing σ with
  | const key levels =>
    simp only [collect] at member
    split at member
    · rename_i h
      rcases List.mem_cons.mp member with rfl | rest
      · obtain ⟨replaced, _, changed⟩ := h
        refine .inr ⟨replaced, ?_⟩
        simp only [subst, replaced, ite_true] at changed ⊢
        cases found : σ'.find? key <;> simp_all
      · exact .inl rest
    · exact .inl member
  | app f a ihf iha =>
    rcases iha member with inner | outer
    · exact ihf inner
    · exact .inr outer
  | lam t b iht ihb | forallE t b iht ihb =>
    rcases ihb member with inner | outer
    · exact iht inner
    · exact .inr outer
  | letE t v b iht ihv ihb =>
    rcases ihb member with inner | outer
    · rcases ihv inner with inner | outer
      · exact iht inner
      · exact .inr outer
    · exact .inr outer
  | proj _ _ v ih => exact ih member
  | _ => exact .inl (by simpa [collect, subst] using member)

private theorem collect_keeps {replaceable : Name → Bool} {σ' σ : Witnesses} {pattern : Shape}
    {name : Name} (found : (σ.find? name).isSome) :
    ((collect replaceable pattern (pattern.subst replaceable σ') σ).find? name).isSome := by
  obtain ⟨witness, found⟩ := Option.isSome_iff_exists.mp found
  simp [collect_extends found]

private theorem subst_collect {replaceable : Name → Bool} {σ' σ₀ σ : Witnesses} {pattern : Shape}
    (agrees : ∀ name witness, σ.find? name = some witness → σ'.find? name = some witness)
    (covers : ∀ name, ((collect replaceable pattern (pattern.subst replaceable σ') σ₀).find? name).isSome →
      (σ.find? name).isSome) :
    pattern.subst replaceable σ = pattern.subst replaceable σ' := by
  induction pattern generalizing σ₀ with
  | const key levels =>
    by_cases replaced : replaceable key = true
    · simp only [subst, replaced, ite_true]
      cases found : σ.find? key with
      | some witness => simp [agrees key witness found]
      | none =>
        have missing := covers key
        rw [found] at missing
        simp only [collect, subst, replaced, ite_true, Option.isSome_none] at missing
        split at missing
        · simp [Witnesses.find?] at missing
        · rename_i kept
          cases known : σ₀.find? key with
          | some _ => simp [known] at missing
          | none =>
            cases found' : σ'.find? key with
            | none => rfl
            | some w => simp_all
    · simp [subst, replaced]
  | app f a ihf iha =>
    simp only [subst]
    rw [ihf (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := a) found), iha covers]
  | lam t b iht ihb =>
    simp only [subst]
    rw [iht (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := b) found), ihb covers]
  | forallE t b iht ihb =>
    simp only [subst]
    rw [iht (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := b) found), ihb covers]
  | letE t v b iht ihv ihb =>
    simp only [subst]
    rw [iht (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := b) (collect_keeps (pattern := v) found)),
      ihv (σ₀ := collect replaceable t (t.subst replaceable σ') σ₀) fun name found =>
        covers name (collect_keeps (pattern := b) found), ihb covers]
  | proj _ _ v ih => simp only [subst]; rw [ih covers]
  | _ => rfl

theorem witnesses?_sound {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (found : pattern.witnesses? replaceable target = some σ) :
    (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  simp only [witnesses?] at found
  split at found
  · rename_i accepted
    cases found
    exact ⟨List.all_eq_true.mp accepted.1, accepted.2⟩
  · cases found

theorem witnesses?_complete {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true)
    (instantiates : pattern.subst replaceable σ = target) :
    (pattern.witnesses? replaceable target).isSome := by
  subst instantiates
  have from_σ := fun (entry : Name × Shape)
      (member : entry ∈ collect replaceable pattern (pattern.subst replaceable σ) []) =>
    (collect_from member).resolve_left (by simp)
  have agrees : ∀ name witness,
      (collect replaceable pattern (pattern.subst replaceable σ) []).find? name = some witness →
      σ.find? name = some witness := fun name witness found => (from_σ _ (find?_mem found)).2
  have allClosed : (collect replaceable pattern (pattern.subst replaceable σ) []).all
      (·.2.closedUnder 0) = true := List.all_eq_true.mpr fun entry member => by
    obtain ⟨replaced, found⟩ := from_σ entry member
    simpa using closed _ (find?_mem found) replaced
  simp [witnesses?, allClosed, subst_collect agrees fun _ found => found]

theorem witnesses?_isSome_iff {replaceable : Name → Bool} {pattern target : Shape} :
    (pattern.witnesses? replaceable target).isSome ↔
      ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  constructor
  · intro found
    obtain ⟨σ, found⟩ := Option.isSome_iff_exists.mp found
    exact ⟨σ, witnesses?_sound found⟩
  · rintro ⟨σ, closed, instantiates⟩
    exact witnesses?_complete (fun entry member _ => closed entry member) instantiates

def independence (headline : Shape) (others : List Shape) : Shape :=
  conjunction (headline.negation :: others)

def independent (replaceable : Name → Bool) (headline : Shape) (others : List Shape) (kill : Shape) : Bool :=
  !replaceable ``And && !replaceable ``Not && !replaceable ``True && !others.isEmpty &&
    ((independence headline others).witnesses? replaceable kill).isSome

private theorem subst_conjunction {replaceable : Name → Bool} {σ : Witnesses}
    (fixed : replaceable ``And = false ∧ replaceable ``True = false) (statements : List Shape) :
    (conjunction statements).subst replaceable σ =
      conjunction (statements.map (·.subst replaceable σ)) := by
  induction statements with
  | nil => simp [conjunction, subst, fixed.2]
  | cons statement rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest => simp only [conjunction, subst, fixed.1] at ih ⊢; simp only [ih, List.map_cons]; rfl

theorem independent_sound {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape}
    (accepted : independent replaceable headline others kill = true) :
    others ≠ [] ∧ ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
      kill = conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) := by
  simp only [independent, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at accepted
  obtain ⟨⟨⟨⟨noAnd, noNot⟩, noTrue⟩, nonempty⟩, found⟩ := accepted
  obtain ⟨σ, found⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨closed, instantiates⟩ := witnesses?_sound found
  refine ⟨nonempty, σ, closed, ?_⟩
  rw [← instantiates, independence, subst_conjunction ⟨noAnd, noTrue⟩]
  simp [negation, subst, noNot]

def existential : List (Universe × Shape) → Shape → Shape
  | [], body => body
  | (level, type) :: rest, body => .app (.app (.const ``Exists [level]) type) (.lam type (existential rest body))

def applicability (premises : List Shape) (inputs : List (Universe × Shape)) (preconditions : List Shape) :
    Shape :=
  premises.foldr .forallE (existential inputs (conjunction preconditions))

def applies (premises : List Shape) (inputs : List (Universe × Shape)) (preconditions : List Shape)
    (witness : Shape) : Bool :=
  !preconditions.isEmpty &&
    ((applicability premises inputs preconditions).witnesses? (fun _ => false) witness).isSome

private theorem subst_unreplaceable (σ : Witnesses) (statement : Shape) :
    statement.subst (fun _ => false) σ = statement := by
  induction statement <;> simp_all [subst]

theorem applies_sound {premises : List Shape} {inputs : List (Universe × Shape)} {preconditions : List Shape}
    {witness : Shape} (accepted : applies premises inputs preconditions witness = true) :
    preconditions ≠ [] ∧ witness = premises.foldr .forallE (existential inputs (conjunction preconditions)) := by
  simp only [applies, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at accepted
  obtain ⟨nonempty, found⟩ := accepted
  obtain ⟨σ, found⟩ := Option.isSome_iff_exists.mp found
  obtain ⟨_, instantiates⟩ := witnesses?_sound found
  exact ⟨nonempty, by rw [← instantiates, subst_unreplaceable]; rfl⟩

end Shape

end SoftwareChallenge

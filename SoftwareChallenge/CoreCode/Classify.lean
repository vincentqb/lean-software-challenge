module

public import SoftwareChallenge.CoreSpec.Statement

public section

namespace SoftwareChallenge

open Lean

def Shape.constants : Shape → List Name
  | .const name _ => [name]
  | .app function argument => function.constants ++ argument.constants
  | .lam type body | .forallE type body => type.constants ++ body.constants
  | .letE type value body => type.constants ++ value.constants ++ body.constants
  | .proj _ _ value => value.constants
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .natLit _ | .strLit _ => []

def Shape.refers (index : Nat) : Shape → Bool
  | .bvar found => found == index
  | .app function argument => function.refers index || argument.refers index
  | .lam type body | .forallE type body => type.refers index || body.refers (index + 1)
  | .letE type value body => type.refers index || value.refers index || body.refers (index + 1)
  | .proj _ _ value => value.refers index
  | .fvar _ | .mvar _ | .sort _ | .const _ _ | .natLit _ | .strLit _ => false

def Shape.concludes? (shape : Shape) : Option Name :=
  match shape.conclusion.appHead with
  | .const name _ => some name
  | _ => none

def ChallengeFacts.isClaim (challenge : ChallengeFacts) : Name → Bool :=
  challenge.claims.contains

namespace Telescope

def depended (telescope : List BinderFact) (index : Nat) : Bool :=
  (List.range telescope.length).any fun later =>
    decide (index < later) && ((telescope[later]?).map fun binder => binder.type.refers (later - 1 - index)).getD false

def kindAt (claims : Name → Bool) (telescope : List BinderFact) (index : Nat) (binder : BinderFact) : BinderKind :=
  if depended telescope index || !binder.prop then .input
  else if binder.meaning.concludes?.any claims then .claim
  else .precondition

def refersAt (index : Nat) (binder : BinderFact) : List Nat :=
  (List.range index).filter fun earlier => binder.type.refers (index - 1 - earlier)

def binderAt (claims replaceable : Name → Bool) (telescope : List BinderFact) (index : Nat) (binder : BinderFact) :
    Binder :=
  { kind := kindAt claims telescope index binder, prop := binder.prop
    mentions := binder.meaning.constants.any replaceable, refers := refersAt index binder }

def summary (claims replaceable : Name → Bool) (telescope : List BinderFact) : List Binder :=
  telescope.zipIdx.map fun (binder, index) => binderAt claims replaceable telescope index binder

end Telescope

def HeadlineFact.binders (challenge : ChallengeFacts) (headline : HeadlineFact) : List Binder :=
  Telescope.summary challenge.isClaim challenge.isReplaceable headline.telescope

def HeadlineFact.claimsWith (claims : Name → Bool) (headline : HeadlineFact) : Array (Nat × Name × String) :=
  (headline.telescope.zipIdx.filterMap fun (binder, index) =>
    if Telescope.kindAt claims headline.telescope index binder == .claim then
      some (index, binder.meaning.concludes?.getD .anonymous, binder.shown)
    else none).toArray

def HeadlineFact.claimed (challenge : ChallengeFacts) (headline : HeadlineFact) : Array (Nat × Name × String) :=
  headline.claimsWith challenge.isClaim

theorem Shape.mem_constants {name : Name} {shape : Shape} : name ∈ shape.constants ↔ shape.Mentions name := by
  induction shape with
  | const constant levels =>
    simp only [Shape.constants, List.mem_singleton]
    constructor
    · rintro rfl
      exact .const levels
    · intro mentions
      cases mentions
      rfl
  | app function argument ihFunction ihArgument =>
    simp only [Shape.constants, List.mem_append, ihFunction, ihArgument]
    constructor
    · rintro (inFunction | inArgument)
      · exact .appFunction inFunction
      · exact .appArgument inArgument
    · intro mentions
      cases mentions with
      | appFunction inFunction => exact .inl inFunction
      | appArgument inArgument => exact .inr inArgument
  | lam type body ihType ihBody =>
    simp only [Shape.constants, List.mem_append, ihType, ihBody]
    constructor
    · rintro (inType | inBody)
      · exact .lamType inType
      · exact .lamBody inBody
    · intro mentions
      cases mentions with
      | lamType inType => exact .inl inType
      | lamBody inBody => exact .inr inBody
  | forallE type body ihType ihBody =>
    simp only [Shape.constants, List.mem_append, ihType, ihBody]
    constructor
    · rintro (inType | inBody)
      · exact .forallEType inType
      · exact .forallEBody inBody
    · intro mentions
      cases mentions with
      | forallEType inType => exact .inl inType
      | forallEBody inBody => exact .inr inBody
  | letE type value body ihType ihValue ihBody =>
    simp only [Shape.constants, List.mem_append, ihType, ihValue, ihBody]
    constructor
    · rintro ((inType | inValue) | inBody)
      · exact .letEType inType
      · exact .letEValue inValue
      · exact .letEBody inBody
    · intro mentions
      cases mentions with
      | letEType inType => exact .inl (.inl inType)
      | letEValue inValue => exact .inl (.inr inValue)
      | letEBody inBody => exact .inr inBody
  | proj structureName index value ih =>
    simp only [Shape.constants, ih]
    constructor
    · exact .proj
    · intro mentions
      cases mentions with
      | proj inValue => exact inValue
  | bvar | fvar | mvar | sort | natLit | strLit =>
    simp only [Shape.constants, List.not_mem_nil, false_iff]
    intro mentions
    cases mentions

theorem Shape.refers_eq_true {index : Nat} {shape : Shape} : shape.refers index = true ↔ shape.Refers index := by
  induction shape generalizing index with
  | bvar found =>
    simp only [Shape.refers, beq_iff_eq]
    constructor
    · rintro rfl
      exact .bvar found
    · intro refers
      cases refers
      rfl
  | app function argument ihFunction ihArgument =>
    simp only [Shape.refers, Bool.or_eq_true, ihFunction, ihArgument]
    constructor
    · rintro (inFunction | inArgument)
      · exact .appFunction inFunction
      · exact .appArgument inArgument
    · intro refers
      cases refers with
      | appFunction inFunction => exact .inl inFunction
      | appArgument inArgument => exact .inr inArgument
  | lam type body ihType ihBody =>
    simp only [Shape.refers, Bool.or_eq_true, ihType, ihBody]
    constructor
    · rintro (inType | inBody)
      · exact .lamType inType
      · exact .lamBody inBody
    · intro refers
      cases refers with
      | lamType inType => exact .inl inType
      | lamBody inBody => exact .inr inBody
  | forallE type body ihType ihBody =>
    simp only [Shape.refers, Bool.or_eq_true, ihType, ihBody]
    constructor
    · rintro (inType | inBody)
      · exact .forallEType inType
      · exact .forallEBody inBody
    · intro refers
      cases refers with
      | forallEType inType => exact .inl inType
      | forallEBody inBody => exact .inr inBody
  | letE type value body ihType ihValue ihBody =>
    simp only [Shape.refers, Bool.or_eq_true, ihType, ihValue, ihBody]
    constructor
    · rintro ((inType | inValue) | inBody)
      · exact .letEType inType
      · exact .letEValue inValue
      · exact .letEBody inBody
    · intro refers
      cases refers with
      | letEType inType => exact .inl (.inl inType)
      | letEValue inValue => exact .inl (.inr inValue)
      | letEBody inBody => exact .inr inBody
  | proj structureName field value ih =>
    simp only [Shape.refers, ih]
    constructor
    · exact .proj
    · intro refers
      cases refers with
      | proj inValue => exact inValue
  | fvar | mvar | sort | const | natLit | strLit =>
    simp only [Shape.refers, Bool.false_eq_true, false_iff]
    intro refers
    cases refers

theorem Shape.concludes?_eq_some {shape : Shape} {claim : Name} :
    shape.concludes? = some claim ↔ shape.Concludes claim := by
  unfold Shape.concludes? Shape.Concludes
  split
  · rename_i name levels found
    rw [found]
    simp only [Option.some.injEq, Shape.const.injEq]
    constructor
    · rintro rfl
      exact ⟨levels, rfl, rfl⟩
    · rintro ⟨_, rfl, -⟩
      rfl
  · rename_i other
    simp only [reduceCtorEq, false_iff, not_exists]
    intro levels found
    exact other claim levels found

theorem Shape.concludes?_any_iff {shape : Shape} {claims : Array Name} :
    shape.concludes?.any claims.contains = true ↔ ∃ claim ∈ claims, shape.Concludes claim := by
  cases found : shape.concludes? with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro claim _ concludes
    rw [← Shape.concludes?_eq_some, found] at concludes
    cases concludes
  | some name =>
    simp only [Option.any_some, Array.contains_iff_mem]
    constructor
    · intro member
      exact ⟨name, member, Shape.concludes?_eq_some.mp found⟩
    · rintro ⟨claim, member, concludes⟩
      rw [← Shape.concludes?_eq_some, found, Option.some.injEq] at concludes
      rw [concludes]
      exact member

namespace Telescope

theorem depended_eq_true {telescope : List BinderFact} {index : Nat} :
    depended telescope index = true ↔ Depended telescope index := by
  unfold depended Depended
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨later, -, earlier, refers⟩
    cases found : telescope[later]? with
    | none => simp [found] at refers
    | some binder =>
      simp only [found, Option.map_some, Option.getD_some] at refers
      exact ⟨later, binder, found, earlier, Shape.refers_eq_true.mp refers⟩
  · rintro ⟨later, binder, found, earlier, refers⟩
    exact ⟨later, (List.getElem?_eq_some_iff.mp found).1, earlier,
      by simp [found, Shape.refers_eq_true.mpr refers]⟩

theorem kindAt_eq_claim_iff {claims : Array Name} {headline : HeadlineFact} {index : Nat} {binder : BinderFact}
    (found : headline.telescope[index]? = some binder) :
    kindAt claims.contains headline.telescope index binder = .claim ↔ headline.Claim claims index := by
  unfold kindAt HeadlineFact.Claim
  rw [← depended_eq_true]
  constructor
  · intro claimed
    split at claimed
    · cases claimed
    · rename_i kept
      split at claimed
      · rename_i concludes
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at kept
        exact ⟨binder, found, kept.2, by simp [kept.1], Shape.concludes?_any_iff.mp concludes⟩
      · cases claimed
  · rintro ⟨same, sameFound, prop, kept, concludes⟩
    rw [found, Option.some.injEq] at sameFound
    subst sameFound
    have notDepended : depended headline.telescope index = false := by simpa using kept
    simp [notDepended, prop, Shape.concludes?_any_iff.mpr concludes]

theorem kindAt_eq_precondition_iff {claims : Array Name} {headline : HeadlineFact} {index : Nat}
    {binder : BinderFact} (found : headline.telescope[index]? = some binder) :
    kindAt claims.contains headline.telescope index binder = .precondition ↔ headline.Precondition claims index := by
  unfold kindAt HeadlineFact.Precondition
  rw [← depended_eq_true]
  constructor
  · intro preconditioned
    split at preconditioned
    · cases preconditioned
    · rename_i kept
      split at preconditioned
      · cases preconditioned
      · rename_i unconcluded
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at kept
        refine ⟨binder, found, kept.2, by simp [kept.1], fun concludes => unconcluded ?_⟩
        exact Shape.concludes?_any_iff.mpr concludes
  · rintro ⟨same, sameFound, prop, kept, unconcluded⟩
    rw [found, Option.some.injEq] at sameFound
    subst sameFound
    have notDepended : depended headline.telescope index = false := by simpa using kept
    have notClaimed : binder.meaning.concludes?.any claims.contains = false := by
      cases claimed : binder.meaning.concludes?.any claims.contains
      · rfl
      · exact absurd (Shape.concludes?_any_iff.mp claimed) unconcluded
    simp [notDepended, prop, notClaimed]

theorem kindAt_ne_claim_iff {claims : Array Name} {headline : HeadlineFact} {index : Nat} {binder : BinderFact}
    (found : headline.telescope[index]? = some binder) :
    kindAt claims.contains headline.telescope index binder ≠ .claim ↔ ¬ headline.Claim claims index := by
  rw [ne_eq, kindAt_eq_claim_iff found]

theorem mentions_any_iff {replaceable : Name → Bool} {binder : BinderFact} :
    binder.meaning.constants.any replaceable = true ↔
      ∃ name, replaceable name = true ∧ binder.meaning.Mentions name := by
  simp only [List.any_eq_true, Shape.mem_constants]
  exact ⟨fun ⟨name, mentions, replaced⟩ => ⟨name, replaced, mentions⟩,
    fun ⟨name, replaced, mentions⟩ => ⟨name, mentions, replaced⟩⟩

theorem refersAt_ne_nil_iff {index : Nat} {binder : BinderFact} : refersAt index binder ≠ [] ↔ binder.Open index := by
  unfold refersAt BinderFact.Open
  rw [ne_eq, List.filter_eq_nil_iff]
  simp only [List.mem_range, Classical.not_forall, Classical.not_not, exists_prop]
  constructor
  · rintro ⟨earlier, bounded, refers⟩
    exact ⟨index - 1 - earlier, by omega, Shape.refers_eq_true.mp refers⟩
  · rintro ⟨earlier, bounded, refers⟩
    refine ⟨index - 1 - earlier, by omega, ?_⟩
    have same : index - 1 - (index - 1 - earlier) = earlier := by omega
    rw [same]
    exact Shape.refers_eq_true.mpr refers

theorem getElem?_summary {claims replaceable : Name → Bool} {telescope : List BinderFact} {index : Nat} :
    (summary claims replaceable telescope)[index]? =
      (telescope[index]?).map (binderAt claims replaceable telescope index) := by
  unfold summary
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases telescope[index]? <;> simp

theorem mem_summary {claims replaceable : Name → Bool} {telescope : List BinderFact} {summarized : Binder} :
    summarized ∈ summary claims replaceable telescope ↔
      ∃ index binder, telescope[index]? = some binder ∧
        summarized = binderAt claims replaceable telescope index binder := by
  rw [List.mem_iff_getElem?]
  simp only [getElem?_summary, Option.map_eq_some_iff]
  exact ⟨fun ⟨index, binder, found, made⟩ => ⟨index, binder, found, made.symm⟩,
    fun ⟨index, binder, found, made⟩ => ⟨index, binder, found, made.symm⟩⟩

end Telescope

theorem HeadlineFact.mem_claimsWith {claims : Array Name} {headline : HeadlineFact} {index : Nat} {claim : Name}
    {statement : String} :
    (index, claim, statement) ∈ headline.claimsWith claims.contains ↔
      ∃ binder, headline.telescope[index]? = some binder ∧ headline.Claim claims index ∧
        binder.meaning.Concludes claim ∧ statement = binder.shown := by
  unfold HeadlineFact.claimsWith
  rw [List.mem_toArray, List.mem_filterMap]
  constructor
  · rintro ⟨⟨binder, at_⟩, member, made⟩
    have found : headline.telescope[at_]? = some binder := List.mem_zipIdx_iff_getElem?.mp member
    dsimp only at made
    split at made
    · rename_i claimed
      have isClaim := (Telescope.kindAt_eq_claim_iff found).mp (beq_iff_eq.mp claimed)
      have concludes : ∃ claim ∈ claims, binder.meaning.Concludes claim := by
        obtain ⟨same, sameFound, -, -, concluded⟩ := isClaim
        have sameBinder : same = binder := Option.some.inj (sameFound.symm.trans found)
        rw [← sameBinder]
        exact concluded
      obtain ⟨named, -, concluded⟩ := concludes
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at made
      obtain ⟨rfl, chosen, rfl⟩ := made
      rw [Shape.concludes?_eq_some.mpr concluded, Option.getD_some] at chosen
      subst chosen
      exact ⟨binder, found, isClaim, concluded, rfl⟩
    · cases made
  · rintro ⟨binder, found, isClaim, concludes, rfl⟩
    refine ⟨(binder, index), List.mem_zipIdx_iff_getElem?.mpr found, ?_⟩
    have claimed := (Telescope.kindAt_eq_claim_iff found).mpr isClaim
    simp [claimed, Shape.concludes?_eq_some.mpr concludes]

theorem HeadlineFact.mem_claimed {challenge : ChallengeFacts} {headline : HeadlineFact} {index : Nat} {claim : Name}
    {statement : String} :
    (index, claim, statement) ∈ headline.claimed challenge ↔
      ∃ binder, headline.telescope[index]? = some binder ∧ headline.Claim challenge.claims index ∧
        binder.meaning.Concludes claim ∧ statement = binder.shown :=
  HeadlineFact.mem_claimsWith

end SoftwareChallenge

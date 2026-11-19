module

@[expose] public section

namespace SoftwareChallenge

inductive BinderKind where
  | input | claim | precondition
  deriving DecidableEq, Repr, Inhabited

structure Binder where
  kind : BinderKind
  mentions : Bool
  refers : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace Telescope

inductive Needed (binders : List Binder) : Nat → Prop where
  | referredInput {index : Nat} {input referrer : Binder} :
      binders[index]? = some input → input.kind = .input → referrer ∈ binders →
      referrer.kind = .precondition → index ∈ referrer.refers → Needed binders index
  | mentioningInput {index : Nat} {input : Binder} :
      binders[index]? = some input → input.kind = .input → input.mentions = true → Needed binders index
  | referredPrecondition {index : Nat} {precondition referrer : Binder} :
      binders[index]? = some precondition → precondition.kind = .precondition → referrer ∈ binders →
      referrer.kind = .precondition → index ∈ referrer.refers → Needed binders index
  | referredByNeeded {index needed : Nat} {binder : Binder} :
      Needed binders needed → binders[needed]? = some binder → index ∈ binder.refers →
      index < binders.length → Needed binders index

def seeded (binders : List Binder) (index : Nat) : Bool :=
  let referred := binders.any fun referrer => referrer.kind == .precondition && referrer.refers.contains index
  match binders[index]? with
  | some binder => match binder.kind with
    | .input => binder.mentions || referred
    | .precondition => referred
    | .claim => false
  | none => false

def expand (binders : List Binder) (needed : List Nat) : List Nat :=
  (List.range binders.length).filter fun index =>
    needed.contains index || needed.any fun other => ((binders[other]?).map (·.refers.contains index)).getD false

def close (binders : List Binder) : Nat → List Nat → List Nat
  | 0, needed => needed
  | rounds + 1, needed => close binders rounds (expand binders needed)

def kept (binders : List Binder) : List Nat :=
  close binders binders.length ((List.range binders.length).filter (seeded binders))

def needsWitness (binders : List Binder) : Bool :=
  binders.any fun binder => binder.mentions && binder.kind != .claim

private theorem mem_expand {binders : List Binder} {needed : List Nat} {index : Nat} :
    index ∈ expand binders needed ↔ index < binders.length ∧
      (index ∈ needed ∨ ∃ other ∈ needed, ∃ binder, binders[other]? = some binder ∧ index ∈ binder.refers) := by
  simp only [expand, List.mem_filter, List.mem_range, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true]
  refine and_congr_right fun _ => or_congr_right ⟨?_, ?_⟩
  · rintro ⟨other, member, refers⟩
    cases found : binders[other]? with
    | none => simp [found] at refers
    | some binder => exact ⟨other, member, binder, found, by simpa [found] using refers⟩
  · rintro ⟨other, member, binder, found, refers⟩
    exact ⟨other, member, by simpa [found] using refers⟩

private theorem nodup_expand (binders : List Binder) (needed : List Nat) : (expand binders needed).Nodup :=
  List.nodup_range.sublist List.filter_sublist

private theorem subset_expand {binders : List Binder} {needed : List Nat}
    (bounded : ∀ index ∈ needed, index < binders.length) : needed ⊆ expand binders needed :=
  fun index member => mem_expand.mpr ⟨bounded index member, .inl member⟩

private theorem expand_congr {binders : List Binder} {needed other : List Nat}
    (same : ∀ index, index ∈ needed ↔ index ∈ other) : expand binders needed = expand binders other := by
  refine List.filter_congr fun index _ => ?_
  have contains : needed.contains index = other.contains index := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact same index
  have any : ∀ test : Nat → Bool, needed.any test = other.any test := fun test => by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    simp only [same]
  rw [contains, any]

private theorem expand_fixed_or_longer {binders : List Binder} {current : List Nat} {rounds : Nat}
    (bounded : ∀ index ∈ current, index < binders.length) (nodup : current.Nodup)
    (previous : expand binders current ⊆ current ∨ rounds ≤ current.length) :
    expand binders (expand binders current) ⊆ expand binders current ∨
      rounds + 1 ≤ (expand binders current).length := by
  have grows := subset_expand bounded
  by_cases fixed : expand binders current ⊆ current
  · refine .inl ?_
    rw [expand_congr fun index => ⟨fun member => fixed member, fun member => grows member⟩]
    exact List.Subset.refl _
  · refine .inr ?_
    obtain ⟨added, fresh, outside⟩ : ∃ added ∈ expand binders current, added ∉ current :=
      Classical.byContradiction fun none => fixed fun added fresh =>
        Classical.byContradiction fun outside => none ⟨added, fresh, outside⟩
    have longer := (List.nodup_cons.mpr ⟨outside, nodup⟩).length_le_of_subset (List.cons_subset.mpr ⟨fresh, grows⟩)
    have := previous.resolve_left fixed
    simp only [List.length_cons] at longer
    omega

private theorem close_succ (binders : List Binder) (rounds : Nat) (needed : List Nat) :
    close binders (rounds + 1) needed = expand binders (close binders rounds needed) := by
  induction rounds generalizing needed with
  | zero => rfl
  | succ rounds ih => exact ih (expand binders needed)

private theorem close_bounded (binders : List Binder) (rounds : Nat) :
    ∀ index ∈ close binders rounds ((List.range binders.length).filter (seeded binders)),
      index < binders.length := by
  cases rounds with
  | zero => exact fun _ member => List.mem_range.mp (List.mem_filter.mp member).1
  | succ rounds => rw [close_succ]; exact fun _ member => (mem_expand.mp member).1

private theorem close_nodup (binders : List Binder) (rounds : Nat) :
    (close binders rounds ((List.range binders.length).filter (seeded binders))).Nodup := by
  cases rounds with
  | zero => exact List.nodup_range.sublist List.filter_sublist
  | succ rounds => rw [close_succ]; exact nodup_expand _ _

private theorem close_fixed_or_long (binders : List Binder) (rounds : Nat) :
    expand binders (close binders rounds ((List.range binders.length).filter (seeded binders))) ⊆
        close binders rounds ((List.range binders.length).filter (seeded binders)) ∨
      rounds ≤ (close binders rounds ((List.range binders.length).filter (seeded binders))).length := by
  induction rounds with
  | zero => exact .inr (Nat.zero_le _)
  | succ rounds ih =>
    rw [close_succ]
    exact expand_fixed_or_longer (close_bounded binders rounds) (close_nodup binders rounds) ih

private theorem kept_fixed (binders : List Binder) : expand binders (kept binders) ⊆ kept binders := by
  rcases close_fixed_or_long binders binders.length with fixed | long
  · exact fixed
  · intro index member
    refine Classical.byContradiction fun outside => ?_
    have longer := (List.nodup_cons.mpr ⟨outside, close_nodup binders binders.length⟩).length_le_of_subset
      (l₂ := List.range binders.length) (List.cons_subset.mpr ⟨List.mem_range.mpr (mem_expand.mp member).1,
        fun other inside => List.mem_range.mpr (close_bounded binders binders.length other inside)⟩)
    simp only [List.length_cons, List.length_range] at longer
    unfold kept at longer
    omega

private theorem seeds_subset_close (binders : List Binder) (rounds : Nat) :
    (List.range binders.length).filter (seeded binders) ⊆
      close binders rounds ((List.range binders.length).filter (seeded binders)) := by
  induction rounds with
  | zero => exact fun _ member => member
  | succ rounds ih =>
    rw [close_succ]
    exact fun _ member => subset_expand (close_bounded binders rounds) (ih member)

private theorem needed_of_seeded {binders : List Binder} {index : Nat} (seed : seeded binders index = true) :
    Needed binders index := by
  have referred : (binders.any fun referrer => referrer.kind == .precondition && referrer.refers.contains index) =
      true → ∃ referrer ∈ binders, referrer.kind = .precondition ∧ index ∈ referrer.refers := by
    simp
  unfold seeded at seed
  cases found : binders[index]? with
  | none => simp [found] at seed
  | some binder =>
    simp only [found] at seed
    cases kind : binder.kind with
    | input =>
      simp only [kind, Bool.or_eq_true] at seed
      rcases seed with mentions | seed
      · exact .mentioningInput found kind mentions
      · obtain ⟨referrer, member, precondition, refers⟩ := referred seed
        exact .referredInput found kind member precondition refers
    | precondition =>
      simp only [kind] at seed
      obtain ⟨referrer, member, precondition, refers⟩ := referred seed
      exact .referredPrecondition found kind member precondition refers
    | claim => simp [kind] at seed

private theorem mem_kept_of_seeded {binders : List Binder} {index : Nat} {binder : Binder}
    (found : binders[index]? = some binder) (seed : seeded binders index = true) : index ∈ kept binders :=
  seeds_subset_close binders binders.length
    (List.mem_filter.mpr ⟨List.mem_range.mpr (List.getElem?_eq_some_iff.mp found).1, seed⟩)

private theorem referred_of_mem {binders : List Binder} {index : Nat} {referrer : Binder} (member : referrer ∈ binders)
    (precondition : referrer.kind = .precondition) (refers : index ∈ referrer.refers) :
    (binders.any fun referrer => referrer.kind == .precondition && referrer.refers.contains index) = true :=
  List.any_eq_true.mpr ⟨referrer, member, by simp [precondition, refers]⟩

theorem kept_iff_needed (binders : List Binder) (index : Nat) :
    index ∈ kept binders ↔ Needed binders index := by
  constructor
  · suffices sound : ∀ rounds, ∀ index ∈ close binders rounds ((List.range binders.length).filter (seeded binders)),
        Needed binders index from sound binders.length index
    intro rounds
    induction rounds with
    | zero => exact fun index member => needed_of_seeded (List.mem_filter.mp member).2
    | succ rounds ih =>
      rw [close_succ]
      intro index member
      obtain ⟨bounded, earlier | ⟨other, inside, binder, found, refers⟩⟩ := mem_expand.mp member
      · exact ih index earlier
      · exact .referredByNeeded (ih other inside) found refers bounded
  · intro needed
    induction needed with
    | referredInput found kind member precondition refers =>
      exact mem_kept_of_seeded found (by simp only [seeded, found, kind, referred_of_mem member precondition refers,
        Bool.or_true])
    | mentioningInput found kind mentions =>
      exact mem_kept_of_seeded found (by simp only [seeded, found, kind, mentions, Bool.true_or])
    | referredPrecondition found kind member precondition refers =>
      exact mem_kept_of_seeded found (by simp only [seeded, found, kind, referred_of_mem member precondition refers])
    | referredByNeeded _ found refers bounded ih =>
      exact kept_fixed binders (mem_expand.mpr ⟨bounded, .inr ⟨_, ih, _, found, refers⟩⟩)

end Telescope

end SoftwareChallenge

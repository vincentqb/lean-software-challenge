module

public import SoftwareChallenge.CoreCode.Rules.Lint
import SoftwareChallenge.Solution.Admits
import SoftwareChallenge.Solution.Format
import all SoftwareChallenge.CoreCode.Rules.Lint
import all SoftwareChallenge.CoreCode.Rules.Standing
import all SoftwareChallenge.CoreCode.Rules.Follows
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

namespace SoftwareChallenge

open Lean

namespace Lint

private theorem filterMap_ite_eq_empty {α β : Type} {xs : Array α} {p : α → Prop} [DecidablePred p] {f : α → β} :
    xs.filterMap (fun x => if p x then none else some (f x)) = #[] ↔ ∀ x ∈ xs, p x := by
  rw [Array.filterMap_eq_empty_iff]
  apply forall₂_congr
  intro x _
  rw [ite_eq_left_iff]
  simp only [reduceCtorEq, imp_false, Classical.not_not]

private theorem ite_singleton_eq_empty {α : Type} {p : Prop} [Decidable p] {x : α} :
    (if p then #[] else #[x]) = #[] ↔ p := by
  by_cases holds : p <;> simp [holds]

theorem unauditedModules_eq_empty_iff (facts : Facts) : unauditedModules facts = #[] ↔
    ∀ source ∈ facts.lake.modules, source.module ≠ facts.challenge.module →
      ∃ fact ∈ facts.solution.inventory.modules, fact.name = source.module :=
  filterMap_ite_eq_empty

theorem unauditedExeRoots_eq_empty_iff (facts : Facts) : unauditedExeRoots facts = #[] ↔
    ∀ root ∈ facts.lake.defaultExeRoots, ∃ fact ∈ facts.solution.inventory.modules, fact.name = root :=
  filterMap_ite_eq_empty

theorem unlintedModules_eq_empty_iff (facts : Facts) : unlintedModules facts = #[] ↔
    ∀ fact ∈ facts.solution.inventory.modules, fact.name ∈ facts.solution.linted :=
  filterMap_ite_eq_empty

theorem lintWarnings_eq_empty_iff (facts : Facts) : lintWarnings facts = #[] ↔ facts.solution.lints = #[] :=
  Array.map_eq_empty_iff

theorem sorries_eq_empty_iff (facts : Facts) : sorries facts = #[] ↔ facts.solution.sorries = #[] :=
  Array.map_eq_empty_iff

private theorem explained_ne_empty (facts : Facts) (violation : Violation) : explained facts violation ≠ #[] := by
  cases violation with
  | axioms declaration found =>
    simp only [explained]
    split
    · simp
    · next nonempty => simpa [Array.isEmpty_iff] using nonempty
  | _ => simp [explained]

theorem violations_eq_empty_iff (facts : Facts) :
    violations facts = #[] ↔ facts.lake.project.Admits facts.solution.inventory := by
  rw [← Project.violations_eq_empty_iff_admits, violations, Array.flatMap_eq_empty_iff]
  constructor
  · intro explainedEmpty
    apply Classical.byContradiction
    intro nonempty
    obtain ⟨violation, member⟩ := Array.exists_mem_of_ne_empty _ nonempty
    exact explained_ne_empty facts violation (explainedEmpty violation member)
  · intro empty violation member
    rw [empty] at member
    simp at member

theorem editableMetaImports_eq_empty_iff (facts : Facts) : editableMetaImports facts = #[] ↔
    ∀ fact ∈ facts.solution.inventory.modules, (Role.ofName fact.name).Owned →
      ∀ dependency ∈ fact.imports, dependency.comptime = true → facts.lake.Builds dependency.name →
        facts.challenge.Owns dependency.name := by
  rw [editableMetaImports, Array.flatMap_eq_empty_iff]
  apply forall₂_congr
  intro fact _
  by_cases owned : (Role.ofName fact.name).Owned
  · simp only [owned, ite_true, true_implies]
    exact filterMap_ite_eq_empty
  · simp [owned]

theorem holesOutsideCode_eq_empty_iff (facts : Facts) : holesOutsideCode facts = #[] ↔
    ∀ hole ∈ facts.challenge.holes, ∀ found ∈ facts.solution.found, found.constant.name = hole.constant.name →
      facts.lake.project.role? found.module = some .coreCode ∨
        facts.lake.project.role? found.module = some .worldCode := by
  rw [holesOutsideCode, Array.flatMap_eq_empty_iff]
  exact forall₂_congr fun _ _ => filterMap_ite_eq_empty

theorem noncomputableHoles_eq_empty_iff (facts : Facts) : noncomputableHoles facts = #[] ↔
    ∀ hole ∈ facts.challenge.holes, ∀ found ∈ facts.solution.found, found.constant.name = hole.constant.name →
      found.compiled = true := by
  rw [noncomputableHoles, Array.flatMap_eq_empty_iff]
  exact forall₂_congr fun _ _ => filterMap_ite_eq_empty

theorem mainOutsidePrograms_eq_empty_iff (facts : Facts) : mainOutsidePrograms facts = #[] ↔
    (facts.lake.Program → ∀ main, facts.solution.main? = some main →
      facts.lake.project.role? main.1 = some .worldCode) := by
  unfold mainOutsidePrograms
  cases found : facts.solution.main? with
  | none => simp
  | some main =>
    simp only [Option.some.injEq]
    rw [ite_singleton_eq_empty]
    exact ⟨fun inWorld program _ same => same ▸ inWorld program, fun all program => all program main rfl⟩

theorem notFixpoints_eq_empty_iff (facts : Facts) : notFixpoints facts = #[] ↔
    ∀ termination ∈ facts.challenge.terminating,
      (∃ found ∈ facts.solution.found, found.constant.name = termination.definition) →
        termination.definition ∈ facts.solution.fixpoints :=
  filterMap_ite_eq_empty

theorem fixpointsWithoutTerminates_eq_empty_iff (facts : Facts) : fixpointsWithoutTerminates facts = #[] ↔
    ∀ hole ∈ facts.challenge.holes, hole.constant.name ∈ facts.solution.fixpoints →
      ∃ termination ∈ facts.challenge.terminating, termination.definition = hole.constant.name :=
  filterMap_ite_eq_empty

theorem misplacedClaims_eq_empty_iff (facts : Facts) : misplacedClaims facts = #[] ↔
    ∀ registration ∈ facts.solution.registrations,
      registration.home? = some registration.module ∧
        facts.lake.project.role? registration.module = some .worldSpec := by
  rw [misplacedClaims, Array.filterMap_eq_empty_iff]
  apply forall₂_congr
  intro registration _
  by_cases home : registration.home? = some registration.module <;>
    by_cases role : facts.lake.project.role? registration.module = some .worldSpec <;> simp [home, role]

theorem unreadableProofs_eq_empty_iff (facts : Facts) : unreadableProofs facts = #[] ↔
    ∀ headline ∈ facts.challenge.headlines, ∀ found ∈ facts.solution.found,
      found.constant.name = headline.target.constant.name → found.constant.kind = .proved →
        found.constant.value? ≠ none := by
  rw [unreadableProofs, Array.flatMap_eq_empty_iff]
  exact forall₂_congr fun _ _ => filterMap_ite_eq_empty

theorem mem_ownedPaths (facts : Facts) (path : String) :
    path ∈ ownedPaths facts ↔ facts.lake.Owned facts.challenge path := by
  simp [ownedPaths, LakeFacts.Owned, Array.mem_push, or_assoc, and_assoc]

theorem unreadOwnedFiles_eq_empty_iff (facts : Facts) : unreadOwnedFiles facts = #[] ↔
    ∀ path, facts.lake.Owned facts.challenge path → facts.files.Digested path := by
  rw [unreadOwnedFiles, filterMap_ite_eq_empty]
  exact ⟨fun digested path owned => digested path ((mem_ownedPaths facts path).mpr owned),
    fun digested path member => digested path ((mem_ownedPaths facts path).mp member)⟩

theorem lockErrors_eq_empty_iff (facts : Facts) : lockErrors facts = #[] ↔ facts.files.LockCurrent := by
  unfold lockErrors FileFacts.LockCurrent
  cases facts.files.lock with
  | missing => simp
  | unreadable problem => simp
  | decoded locked => simp [Lock.violations_eq_empty_iff]

theorem solutionErrors_eq_empty_iff (facts : Facts) : solutionErrors facts = #[] ↔ facts.lake.OneSolution :=
  ite_singleton_eq_empty

theorem targetErrors_eq_empty_iff (facts : Facts) : targetErrors facts = #[] ↔ `statement ∈ facts.lake.defaultTargets :=
  ite_singleton_eq_empty

theorem challengeImports_eq_empty_iff (facts : Facts) : challengeImports facts = #[] ↔
    ∀ line ∈ facts.solution.imports, line.fact.name ≠ facts.challenge.module :=
  filterMap_ite_eq_empty

theorem builtinLintErrors_eq_empty_iff (facts : Facts) : builtinLintErrors facts = #[] ↔
    facts.lake.builtinLint = none := by
  unfold builtinLintErrors
  cases facts.lake.builtinLint <;> simp


private theorem firstModules_spec (declarations : List DeclarationFact) (init : Std.HashMap Name Name) :
    let result := declarations.foldl (fun first fact =>
      if first.contains fact.name then first else first.insert fact.name fact.module) init
    (∀ key module, result[key]? = some module →
      init[key]? = some module ∨ ∃ fact ∈ declarations, fact.name = key ∧ fact.module = module) ∧
    (∀ key, init.contains key = true → result.contains key = true) ∧
    (∀ fact ∈ declarations, result.contains fact.name = true) := by
  induction declarations generalizing init with
  | nil => exact ⟨fun _ _ found => .inl found, fun _ contained => contained, fun _ member => absurd member (by simp)⟩
  | cons fact rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨recorded, kept, covered⟩ := ih (if init.contains fact.name then init else init.insert fact.name fact.module)
    refine ⟨fun key module found => ?_, fun key contained => kept key ?_, fun other member => ?_⟩
    · rcases recorded key module found with earlier | later
      · by_cases present : init.contains fact.name = true
        · simp only [present, ite_true] at earlier
          exact .inl earlier
        · simp only [present, Bool.false_eq_true, ite_false, Std.HashMap.getElem?_insert] at earlier
          split at earlier
          · next same =>
            simp only [Option.some.injEq] at earlier
            exact .inr ⟨fact, by simp, by simpa using same, earlier⟩
          · exact .inl earlier
      · obtain ⟨other, member, named, moduled⟩ := later
        exact .inr ⟨other, by simp [member], named, moduled⟩
    · split
      · exact contained
      · simp [Std.HashMap.contains_insert, contained]
    · rcases List.mem_cons.mp member with same | later
      · subst same
        apply kept
        split
        · assumption
        · simp [Std.HashMap.contains_insert]
      · exact covered other later

theorem duplicatesIn_eq_empty_iff (declarations : Array DeclarationFact) : duplicatesIn declarations = #[] ↔
    ∀ fact ∈ declarations, ∀ other ∈ declarations, fact.name = other.name → fact.module = other.module := by
  obtain ⟨recorded, -, covered⟩ := firstModules_spec declarations.toList {}
  simp only [Array.foldl_toList] at recorded covered
  have present : ∀ fact ∈ declarations,
      ∃ module, (firstModules declarations)[fact.name]? = some module := by
    intro fact member
    have contained := covered fact (Array.mem_toList_iff.mpr member)
    rw [Std.HashMap.contains_eq_isSome_getElem?] at contained
    exact Option.isSome_iff_exists.mp contained
  have kept : ∀ fact ∈ declarations, ∀ module,
      (firstModules declarations)[fact.name]? = some module →
        ∃ other ∈ declarations, other.name = fact.name ∧ other.module = module := by
    intro fact _ module found
    rcases recorded fact.name module found with initial | ⟨other, member, named, moduled⟩
    · rw [Std.HashMap.getElem?_empty] at initial
      cases initial
    · exact ⟨other, Array.mem_toList_iff.mp member, named, moduled⟩
  simp only [duplicatesIn, Array.filterMap_eq_empty_iff]
  constructor
  · intro unique fact member other otherMember named
    obtain ⟨module, found⟩ := present fact member
    obtain ⟨otherModule, otherFound⟩ := present other otherMember
    have first := unique fact member
    have second := unique other otherMember
    rw [found] at first
    rw [otherFound] at second
    simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Classical.not_not] at first second
    rw [named, otherFound] at found
    simp only [Option.some.injEq] at found
    rw [← first, ← second, found]
  · intro once fact member
    split
    · next module found =>
      obtain ⟨other, otherMember, named, moduled⟩ := kept fact member module found
      have same : module = fact.module := moduled ▸ once other otherMember fact member named
      simp [same]
    · rfl


theorem counted_eq_true {lake : LakeFacts} {fact : DeclarationFact} :
    counted lake fact = true ↔ fact.Counted lake := by
  unfold counted DeclarationFact.Counted
  by_cases named : fact.name = `main <;> simp [named]

theorem duplicates_eq_empty_iff (facts : Facts) : duplicates facts = #[] ↔
    ∀ fact ∈ facts.solution.inventory.declarations, ∀ other ∈ facts.solution.inventory.declarations,
      fact.Counted facts.lake → other.Counted facts.lake → fact.name = other.name → fact.module = other.module := by
  rw [duplicates, duplicatesIn_eq_empty_iff]
  simp only [Array.mem_filter, counted_eq_true]
  constructor
  · intro once fact member other otherMember counted otherCounted named
    exact once fact ⟨member, counted⟩ other ⟨otherMember, otherCounted⟩ named
  · rintro once fact ⟨member, counted⟩ other ⟨otherMember, otherCounted⟩ named
    exact once fact member other otherMember counted otherCounted named


theorem comparatorErrors_eq_empty_iff (facts : Facts) : comparatorErrors facts = #[] ↔
    ∃ solution ∈ facts.lake.modules, Name.NamedSolution solution.module ∧
      facts.files.comparator = .decoded (Config.expected facts.challenge solution.module) := by
  unfold comparatorErrors
  cases facts.files.comparator with
  | missing => simp
  | unreadable problem => simp
  | decoded config =>
    simp only [Decoded.decoded.injEq]
    split
    · next found =>
      simp only [true_iff]
      obtain ⟨source, member, matched⟩ := Array.any_eq_true'.mp found
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at matched
      exact ⟨source, member, matched⟩
    · next missing =>
      refine ⟨fun empty => absurd empty (by simp), ?_⟩
      rintro ⟨source, member, named, matched⟩
      exact absurd (Array.any_eq_true'.mpr ⟨source, member, by simp [named, matched]⟩) missing

theorem holds_iff (solution : SolutionFacts) (target : TargetFact) :
    solution.holds target = true ↔ solution.Holds target := by
  simp only [SolutionFacts.holds, SolutionFacts.proves, FoundFact.restates, SolutionFacts.present,
    SolutionFacts.Holds, Array.any_eq_true', Array.all_eq_true', Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem,
    and_assoc]

theorem unproved_eq_empty_iff (facts : Facts) (targets : Array TargetFact) :
    unproved facts targets = #[] ↔ ∀ target ∈ targets, facts.solution.Holds target := by
  rw [unproved, filterMap_ite_eq_empty]
  simp only [holds_iff]

private theorem calls_iff (solution : SolutionFacts) (caller callee : Name) :
    callee ∈ (callGraph solution).next caller ↔ solution.Calls caller callee := by
  simp only [callGraph, Graph.mem_next_ofEdges, SolutionFacts.Calls]
  exact ⟨fun ⟨targets, member, inside⟩ => ⟨(caller, targets), member, rfl, inside⟩,
    fun ⟨entry, member, named, inside⟩ => ⟨entry.2, named ▸ member, inside⟩⟩

private theorem transGen_of_reaches {solution : SolutionFacts} {source middle target : Name}
    (first : solution.Calls source middle) (path : (callGraph solution).Reaches middle target) :
    Relation.TransGen solution.Calls source target := by
  induction path with
  | refl => exact .single first
  | step _ last ih => exact .tail ih ((calls_iff _ _ _).mp last)

private theorem reaches_of_transGen {solution : SolutionFacts} {source target : Name}
    (path : Relation.TransGen solution.Calls source target) :
    ∃ middle, solution.Calls source middle ∧ (callGraph solution).Reaches middle target := by
  induction path with
  | single first => exact ⟨_, first, .refl _⟩
  | tail _ last ih =>
    obtain ⟨middle, first, rest⟩ := ih
    exact ⟨middle, first, .step rest ((calls_iff _ _ _).mpr last)⟩

theorem reachedFromMain_iff (solution : SolutionFacts) (name : Name) :
    (reachedFromMain solution).contains name = true ↔ Relation.TransGen solution.Calls `main name := by
  simp only [reachedFromMain]
  rw [Std.HashSet.contains_iff_mem, Graph.mem_closure_iff]
  constructor
  · rintro ⟨middle, first, path⟩
    exact transGen_of_reaches ((calls_iff _ _ _).mp first) path
  · intro path
    obtain ⟨middle, first, rest⟩ := reaches_of_transGen path
    exact ⟨middle, (calls_iff _ _ _).mpr first, rest⟩

theorem mainItems_eq_empty_iff (facts : Facts)
    (defined : ∀ hole ∈ facts.challenge.holes, facts.solution.Holds hole) : mainItems facts = #[] ↔
    (facts.lake.Program → (∃ main, facts.solution.main? = some main) ∧
      ∀ hole ∈ facts.challenge.holes, Relation.TransGen facts.solution.Calls `main hole.constant.name) := by
  unfold mainItems
  by_cases program : facts.lake.Program
  · simp only [program, ite_true, true_implies]
    cases found : facts.solution.main? with
    | none => simp
    | some main =>
      simp only [Array.map_eq_empty_iff, Array.filter_eq_empty_iff, Bool.and_eq_true, Bool.not_eq_true',
        not_and, Bool.not_eq_false, reachedFromMain_iff, holds_iff]
      exact ⟨fun reached => ⟨⟨main, rfl⟩, fun hole member => reached hole member (defined hole member)⟩,
        fun ⟨_, reached⟩ hole member _ => reached hole member⟩
  · simp [program]

theorem undecidedChecks_eq_empty_iff (facts : Facts) : undecidedChecks facts = #[] ↔
    ∀ use ∈ facts.solution.claimUses, ∀ check ∈ use.checks, check.2 ≠ .undecided := by
  rw [undecidedChecks, Array.flatMap_eq_empty_iff]
  exact forall₂_congr fun _ _ => filterMap_ite_eq_empty

theorem uncheckedClaims_eq_empty_iff (facts : Facts) : uncheckedClaims facts = #[] ↔
    ∀ headline ∈ facts.challenge.headlines, ∀ index, headline.Claim facts.challenge.claims index →
      ∃ use ∈ facts.solution.claimUses, use.headline = headline.target.constant.name ∧ use.binder = index ∧
        ∃ check ∈ use.checks, check.2 = .matched := by
  rw [uncheckedClaims, Array.flatMap_eq_empty_iff]
  apply forall₂_congr
  intro headline _
  rw [Array.filterMap_eq_empty_iff]
  constructor
  · intro covered index claimed
    obtain ⟨binder, found, -, -, claim, -, concludes⟩ := id claimed
    have listed := covered _ (HeadlineFact.mem_claimed.mpr ⟨binder, found, claimed, concludes, rfl⟩)
    simpa only [ite_eq_left_iff, reduceCtorEq, imp_false, Classical.not_not] using listed
  · rintro covered ⟨index, claim, statement⟩ listed
    obtain ⟨-, -, claimed, -, -⟩ := HeadlineFact.mem_claimed.mp listed
    simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Classical.not_not]
    exact covered index claimed

theorem hiddenDependencies_eq_empty_iff (facts : Facts) : hiddenDependencies facts = #[] ↔
    ∀ package ∈ facts.lake.packages, package.Visible facts.lake.packageDir :=
  filterMap_ite_eq_empty

theorem errorsOf_eq_empty_iff (facts : Facts) : errorsOf facts = #[] ↔ Lint.Clean facts := by
  simp only [errorsOf, Array.append_eq_empty_iff, unauditedModules_eq_empty_iff, unauditedExeRoots_eq_empty_iff,
    violations_eq_empty_iff, duplicates_eq_empty_iff, holesOutsideCode_eq_empty_iff,
    noncomputableHoles_eq_empty_iff, fixpointsWithoutTerminates_eq_empty_iff, notFixpoints_eq_empty_iff,
    mainOutsidePrograms_eq_empty_iff, misplacedClaims_eq_empty_iff, unreadableProofs_eq_empty_iff,
    editableMetaImports_eq_empty_iff, sorries_eq_empty_iff, unlintedModules_eq_empty_iff,
    lintWarnings_eq_empty_iff, builtinLintErrors_eq_empty_iff, challengeImports_eq_empty_iff,
    solutionErrors_eq_empty_iff, targetErrors_eq_empty_iff, unreadOwnedFiles_eq_empty_iff,
    lockErrors_eq_empty_iff, comparatorErrors_eq_empty_iff, and_assoc]
  constructor
  · rintro ⟨modulesAudited, exeRootsAudited, admitted, declaredOnce, holesInCode, holesCompiled,
      fixpointsTerminate, fixpointsDeclared, mainInWorldCode, claimsDeclared, proofsReadable, specMetaImportsOwned,
      noSorry, lintersCover, lintersPass, builtinLintOff, challengeUnimported, oneSolution, statementTarget,
      ownedDigested, lockCurrent, comparatorCurrent⟩
    exact ⟨modulesAudited, exeRootsAudited, lintersCover, lintersPass, noSorry, admitted, specMetaImportsOwned,
      declaredOnce, holesInCode, holesCompiled, mainInWorldCode, fixpointsDeclared, fixpointsTerminate,
      claimsDeclared, proofsReadable, ownedDigested, lockCurrent, comparatorCurrent, oneSolution, statementTarget,
      challengeUnimported, builtinLintOff⟩
  · intro clean
    exact ⟨clean.modulesAudited, clean.exeRootsAudited, clean.admitted, clean.declaredOnce, clean.holesInCode,
      clean.holesCompiled, clean.fixpointsTerminate, clean.fixpointsDeclared, clean.mainInWorldCode,
      clean.claimsDeclared, clean.proofsReadable, clean.specMetaImportsOwned, clean.noSorry, clean.lintersCover,
      clean.lintersPass, clean.builtinLintOff, clean.challengeUnimported, clean.oneSolution, clean.statementTarget,
      clean.ownedDigested, clean.lockCurrent, clean.comparatorCurrent⟩

theorem pendingOf_eq_empty_iff (facts : Facts) : pendingOf facts = #[] ↔
    (∀ headline ∈ facts.challenge.headlines, facts.solution.Holds headline.target) ∧
    (∀ hole ∈ facts.challenge.holes, facts.solution.Holds hole) ∧
    (∀ kill ∈ facts.challenge.kills, facts.solution.Holds kill.target) ∧
    (∀ witness ∈ facts.challenge.witnesses, facts.solution.Holds witness.target) ∧
    (facts.lake.Program → (∃ main, facts.solution.main? = some main) ∧
      ∀ hole ∈ facts.challenge.holes, Relation.TransGen facts.solution.Calls `main hole.constant.name) ∧
    (∀ use ∈ facts.solution.claimUses, ∀ check ∈ use.checks, check.2 ≠ .undecided) ∧
    (∀ headline ∈ facts.challenge.headlines, ∀ index, headline.Claim facts.challenge.claims index →
      ∃ use ∈ facts.solution.claimUses, use.headline = headline.target.constant.name ∧ use.binder = index ∧
        ∃ check ∈ use.checks, check.2 = .matched) ∧
    (∀ package ∈ facts.lake.packages, package.Visible facts.lake.packageDir) := by
  simp only [pendingOf, Array.append_eq_empty_iff, unproved_eq_empty_iff, Array.forall_mem_map,
    undecidedChecks_eq_empty_iff, uncheckedClaims_eq_empty_iff, hiddenDependencies_eq_empty_iff, and_assoc]
  constructor
  · rintro ⟨headlines, holes, kills, witnesses, main, decided, checked, visible⟩
    exact ⟨headlines, holes, kills, witnesses, (mainItems_eq_empty_iff facts holes).mp main, decided, checked,
      visible⟩
  · rintro ⟨headlines, holes, kills, witnesses, main, decided, checked, visible⟩
    exact ⟨headlines, holes, kills, witnesses, (mainItems_eq_empty_iff facts holes).mpr main, decided, checked,
      visible⟩

private theorem groupImpure_empty (facts : Facts) : groupImpure facts #[] = #[] := rfl

private theorem withoutRepeatedSorries_empty (facts : Facts) : withoutRepeatedSorries facts #[] = #[] := rfl

theorem reported_eq_empty_iff (facts : Facts) (errors : Array Error) :
    reported facts errors = #[] ↔ errors = #[] := by
  unfold reported
  dsimp only
  split
  · exact Iff.rfl
  · next kept =>
    constructor
    · intro empty
      exact absurd (Array.isEmpty_iff.mpr empty) kept
    · intro empty
      subst empty
      rw [groupImpure_empty, Array.filter_empty, withoutRepeatedSorries_empty] at kept
      exact absurd rfl kept

theorem code_eq_zero_iff (errors : Array Error) (pending : Array Pending) :
    code errors pending = 0 ↔ errors = #[] ∧ pending = #[] := by
  unfold code
  cases noErrors : errors.isEmpty <;> cases noPending : pending.isEmpty <;>
    simp_all [Array.isEmpty_iff, Array.isEmpty_eq_false_iff]

theorem code_ne_one_iff (errors : Array Error) (pending : Array Pending) :
    code errors pending ≠ 1 ↔ errors = #[] := by
  unfold code
  cases noErrors : errors.isEmpty <;> cases noPending : pending.isEmpty <;>
    simp_all [Array.isEmpty_iff, Array.isEmpty_eq_false_iff]

private theorem lockErrors_eq_empty_of_clean (facts : Facts) (clean : errorsOf facts = #[]) : lockErrors facts = #[] := by
  simp only [errorsOf, Array.append_eq_empty_iff] at clean
  exact clean.1.2

theorem drifted_eq_false (facts : Facts) (clean : errorsOf facts = #[]) : drifted facts = false := by
  unfold drifted
  split
  · rfl
  · simp [lockErrors_eq_empty_of_clean facts clean]

end Lint

theorem Lint.run_code_eq_zero_iff (facts : Facts) : (Lint.run facts).code = 0 ↔ Lint.Complete facts := by
  simp only [Lint.run, Lint.code_eq_zero_iff, Lint.reported_eq_empty_iff]
  constructor
  · rintro ⟨clean, pending⟩
    rw [Lint.drifted_eq_false facts clean] at pending
    obtain ⟨headlinesProved, holesDefined, killsProved, witnessesProved, mainReachesHoles, checksDecided,
      claimsChecked, dependenciesVisible⟩ := (Lint.pendingOf_eq_empty_iff facts).mp pending
    exact ⟨(Lint.errorsOf_eq_empty_iff facts).mp clean, headlinesProved, holesDefined, killsProved, witnessesProved,
      mainReachesHoles, claimsChecked, checksDecided, dependenciesVisible⟩
  · intro complete
    have clean := (Lint.errorsOf_eq_empty_iff facts).mpr complete.toClean
    rw [Lint.drifted_eq_false facts clean]
    exact ⟨clean, (Lint.pendingOf_eq_empty_iff facts).mpr ⟨complete.headlinesProved, complete.holesDefined,
      complete.killsProved, complete.witnessesProved, complete.mainReachesHoles, complete.checksDecided,
      complete.claimsChecked, complete.dependenciesVisible⟩⟩

theorem Lint.run_code_ne_one_iff (facts : Facts) : (Lint.run facts).code ≠ 1 ↔ Lint.Clean facts := by
  simp only [Lint.run, Lint.code_ne_one_iff, Lint.reported_eq_empty_iff, Lint.errorsOf_eq_empty_iff]

theorem Lint.run_code_ne_zero_iff (facts : Facts) :
    (Lint.run facts).code ≠ 0 ↔ (Lint.run facts).errors ≠ #[] ∨ (Lint.run facts).pending ≠ #[] := by
  simp only [Lint.run, ne_eq, Lint.code_eq_zero_iff, Classical.not_and_iff_not_or_not]

private def killLake : LakeFacts :=
  { packageDir := "/work", configFiles := #["lakefile.lean"],
    modules := #[⟨`App.Solution, "App/Solution.lean"⟩], challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩],
    defaultExeRoots := #[], packages := #[], defaultTargets := #[`statement], builtinLint := none, testDriver := "software_challenge/test_challenge",
    testDriverArgs := #[], testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, ownTests := #[], inputs := #[] }

private def killChallenge : ChallengeFacts :=
  { module := `Challenge, file := "Challenge.lean", runtimeImports := #[], metaImports := #[], closure := #[],
    headlines := #[], kills := #[], witnesses := #[], holes := #[], filled := #[], axioms := #[], terminating := #[],
    replaceable := #[] }

private def killDigests : Array Lock.Entry :=
  #[⟨"lakefile.lean", "1"⟩, ⟨"Challenge.lean", "2"⟩, ⟨"App/Solution.lean", "3"⟩]

private def killFiles : FileFacts :=
  { lock := .decoded killDigests, digests := killDigests,
    comparator := .decoded (Config.expected killChallenge `App.Solution) }

private def killModule : ModuleFact :=
  { name := `App.Solution, file := "App/Solution.lean", usesModuleSystem := true, imports := #[] }

private def killSolution : SolutionFacts :=
  { solution? := some `App.Solution, inventory := ⟨#[killModule], #[]⟩, blames := #[], imports := #[],
    calls := #[], proofUses := #[], meanings := #[], found := #[], solutionClosure := #[], importsSolution := #[],
    premiseUses := #[], claimUses := #[], checks := #[], registrations := #[], lints := #[],
    linted := #[`App.Solution], sorries := #[], fixpoints := #[], main? := none, places := #[] }

private def killFacts : Facts :=
  { lake := killLake, files := killFiles, challenge := killChallenge, solution := killSolution }

private theorem killOwnedDigested (path : String) (owned : killLake.Owned killChallenge path) :
    killFiles.Digested path := by
  rcases owned with listed | named | ⟨source, listed, -, filed⟩
  · simp [killLake] at listed
    exact ⟨⟨"lakefile.lean", "1"⟩, by simp [killFiles, killDigests], listed.symm⟩
  · exact ⟨⟨"Challenge.lean", "2"⟩, by simp [killFiles, killDigests], named.symm⟩
  · simp [killLake] at listed
    subst listed
    exact ⟨⟨"App/Solution.lean", "3"⟩, by simp [killFiles, killDigests], filed⟩

private theorem killOneSolution : killLake.OneSolution :=
  ⟨⟨`App.Solution, "App/Solution.lean"⟩, by simp [killLake], rfl, fun other member _ => by
    simp [killLake] at member; simp [member]⟩

private theorem killComplete : Lint.Complete killFacts where
  modulesAudited := fun source member _ => by
    simp [killFacts, killLake] at member
    subst member
    exact ⟨killModule, by simp [killFacts, killSolution], rfl⟩
  exeRootsAudited := by simp [killFacts, killLake]
  lintersCover := by simp [killFacts, killSolution, killModule]
  lintersPass := rfl
  noSorry := rfl
  admitted := {
    placed := fun fact member => by
      simp [killFacts, killSolution] at member
      subst member
      exact ⟨_, by simp [Project.role?, LakeFacts.project, killFacts, killLake, killModule]; rfl⟩
    modular := by simp [killFacts, killSolution, killModule]
    layered := by simp [killFacts, killSolution, killModule]
    pure := by simp [killFacts, killSolution] }
  specMetaImportsOwned := by simp [killFacts, killSolution, killModule]
  declaredOnce := by simp [killFacts, killSolution]
  holesInCode := by simp [killFacts, killChallenge]
  holesCompiled := by simp [killFacts, killChallenge]
  mainInWorldCode := fun _ main found => by simp [killFacts, killSolution] at found
  fixpointsDeclared := by simp [killFacts, killChallenge]
  fixpointsTerminate := by simp [killFacts, killChallenge]
  claimsDeclared := by simp [killFacts, killSolution]
  proofsReadable := by simp [killFacts, killChallenge]
  ownedDigested := killOwnedDigested
  lockCurrent := ⟨killDigests, rfl, fun _ => rfl⟩
  comparatorCurrent := ⟨⟨`App.Solution, "App/Solution.lean"⟩, by simp [killFacts, killLake], rfl, rfl⟩
  oneSolution := killOneSolution
  statementTarget := by simp [killFacts, killLake]
  challengeUnimported := by simp [killFacts, killSolution]
  builtinLintOff := rfl
  headlinesProved := by simp [killFacts, killChallenge]
  holesDefined := by simp [killFacts, killChallenge]
  killsProved := by simp [killFacts, killChallenge]
  witnessesProved := by simp [killFacts, killChallenge]
  mainReachesHoles := fun ⟨root, member, _⟩ => by simp [killFacts, killLake] at member
  claimsChecked := by simp [killFacts, killChallenge]
  checksDecided := by simp [killFacts, killSolution]
  dependenciesVisible := by simp [killFacts, killLake]

private def builtinLinted : Facts :=
  { killFacts with lake := { killLake with builtinLint := some ⟨"lakefile.lean", 5⟩ } }

private theorem builtinLinted_unclean : ¬ Lint.Clean builtinLinted := fun clean => by
  have off := clean.builtinLintOff
  simp [builtinLinted] at off

theorem Lint.run_code_eq_zero_iff_rejects_accepting :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 0 } : Lint.Result))
        facts).code = 0 ↔ Lint.Complete facts := fun holds =>
  builtinLinted_unclean ((holds builtinLinted).mp rfl).toClean

theorem Lint.run_code_eq_zero_iff_rejects_refusing :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
        facts).code = 0 ↔ Lint.Complete facts := fun holds =>
  absurd ((holds killFacts).mpr killComplete) (by decide)

theorem Lint.run_code_ne_one_iff_rejects_accepting :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 0 } : Lint.Result))
        facts).code ≠ 1 ↔ Lint.Clean facts := fun holds =>
  builtinLinted_unclean ((holds builtinLinted).mp (by decide))

theorem Lint.run_code_ne_one_iff_rejects_refusing :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
        facts).code ≠ 1 ↔ Lint.Clean facts := fun holds =>
  (holds killFacts).mpr killComplete.toClean rfl

theorem Lint.run_code_ne_zero_iff_rejects_accepting :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) =>
        ({ errors := #[.noStatementTarget], pending := #[], report := #[], code := 0 } : Lint.Result))
          facts).code ≠ 0 ↔
        ((fun (_ : Facts) =>
          ({ errors := #[.noStatementTarget], pending := #[], report := #[], code := 0 } : Lint.Result))
            facts).errors ≠ #[] ∨
        ((fun (_ : Facts) =>
          ({ errors := #[.noStatementTarget], pending := #[], report := #[], code := 0 } : Lint.Result))
            facts).pending ≠ #[] := fun holds =>
  (holds default).mpr (.inl (by simp)) rfl

theorem Lint.run_code_ne_zero_iff_rejects_refusing :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
        facts).code ≠ 0 ↔
        ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
          facts).errors ≠ #[] ∨
        ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
          facts).pending ≠ #[] := fun holds => by
  have refused := (holds default).mp (by decide)
  simp at refused

end SoftwareChallenge

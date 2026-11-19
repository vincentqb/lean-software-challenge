module

public import SoftwareChallenge.CoreCode.Rules.Test
import all SoftwareChallenge.CoreCode.Rules.Test

public section

namespace SoftwareChallenge

open Lean

namespace Test

theorem sameCheck_iff {left right : CheckFact} : sameCheck left right = true ↔ left = right := by
  obtain ⟨claim, statement, ⟨file, line⟩⟩ := left
  obtain ⟨claim', statement', ⟨file', line'⟩⟩ := right
  simp [sameCheck, samePlace, and_assoc]

theorem sameKind_iff {left right : OwnTestKind} : sameKind left right = true ↔ left = right := by
  cases left <;> cases right <;> simp [sameKind]

theorem sameOwnTest_iff {left right : OwnTestFact} : sameOwnTest left right = true ↔ left = right := by
  obtain ⟨name, kind, ⟨file, line⟩⟩ := left
  obtain ⟨name', kind', ⟨file', line'⟩⟩ := right
  simp [sameOwnTest, sameKind_iff, samePlace, and_assoc]

private theorem filterMap_ite_eq_empty {α β : Type} {xs : Array α} {p : α → Prop} [DecidablePred p] {f : α → β} :
    xs.filterMap (fun x => if p x then none else some (f x)) = #[] ↔ ∀ x ∈ xs, p x := by
  rw [Array.filterMap_eq_empty_iff]
  apply forall₂_congr
  intro x _
  rw [ite_eq_left_iff]
  simp only [reduceCtorEq, imp_false, Classical.not_not]

theorem failedChecks_eq_empty_iff (facts : TestFacts) :
    failedChecks facts = #[] ↔ ∀ outcome ∈ facts.checks, outcome.error? = none := by
  simp [failedChecks, Array.filterMap_eq_empty_iff]

theorem checksNotRun_eq_empty_iff (facts : TestFacts) :
    checksNotRun facts = #[] ↔ ∀ check ∈ facts.declaredChecks, ∃ outcome ∈ facts.checks, outcome.check = check := by
  rw [checksNotRun, filterMap_ite_eq_empty]
  simp only [Array.any_eq_true', sameCheck_iff]

theorem failedOwnTests_eq_empty_iff (facts : TestFacts) :
    failedOwnTests facts = #[] ↔ ∀ run ∈ facts.ownTests, run.code = 0 :=
  filterMap_ite_eq_empty

theorem ownTestsNotRun_eq_empty_iff (facts : TestFacts) :
    ownTestsNotRun facts = #[] ↔ ∀ test ∈ facts.declaredOwnTests, ∃ run ∈ facts.ownTests, run.test = test := by
  rw [ownTestsNotRun, filterMap_ite_eq_empty]
  simp only [Array.any_eq_true', sameOwnTest_iff]

theorem undeclaredOwnTests_eq_empty_iff (facts : TestFacts) :
    undeclaredOwnTests facts = #[] ↔ facts.unknownOwnTests = #[] := by
  simp [undeclaredOwnTests]

theorem failuresOf_eq_empty_iff (facts : TestFacts) : failuresOf facts = #[] ↔ Test.Complete facts := by
  simp only [failuresOf, Array.append_eq_empty_iff, failedChecks_eq_empty_iff, checksNotRun_eq_empty_iff,
    failedOwnTests_eq_empty_iff, ownTestsNotRun_eq_empty_iff, undeclaredOwnTests_eq_empty_iff]
  constructor
  · rintro ⟨⟨⟨⟨passed, run⟩, ownPassed⟩, ownRun⟩, declared⟩
    exact ⟨run, passed, ownRun, ownPassed, declared⟩
  · intro complete
    exact ⟨⟨⟨⟨complete.checksPass, complete.checksRun⟩, complete.ownTestsPass⟩, complete.ownTestsRun⟩,
      complete.ownTestsDeclared⟩

theorem code_eq_zero_iff (failures : Array Failure) : code failures = 0 ↔ failures = #[] := by
  unfold code
  cases empty : failures.isEmpty
  · have nonempty : failures ≠ #[] := Array.isEmpty_eq_false_iff.mp empty
    simp only [Bool.false_eq_true, ite_false, nonempty, iff_false]
    split
    · decide
    · assumption
  · simp [Array.isEmpty_iff.mp empty]

theorem Failure.code_le_one (failure : Failure) : failure.code ≤ 1 := by
  cases failure <;> exact (by decide : (1 : UInt32) ≤ 1)

theorem worst_le_one (failures : List Failure) (worst : UInt32) (bounded : worst ≤ 1) :
    failures.foldl (fun worst failure => max worst failure.code) worst ≤ 1 := by
  induction failures generalizing worst with
  | nil => exact bounded
  | cons failure rest ih =>
    apply ih
    by_cases higher : worst ≤ failure.code
    · simpa [max, maxOfLe, higher] using failure.code_le_one
    · simpa [max, maxOfLe, higher] using bounded

end Test

theorem Test.run_code_le_one (facts : TestFacts) : (Test.run facts).code ≤ 1 := by
  simp only [Test.run, Test.code]
  split
  · decide
  · split
    · decide
    · rw [← Array.foldl_toList]
      exact Test.worst_le_one _ 0 (by decide)

theorem Test.run_code_le_one_rejects_unjudged :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 2 } : Test.Result)) facts).code ≤ 1 :=
  fun holds => absurd (holds default) (by decide)

theorem Test.run_code_eq_zero_iff (facts : TestFacts) : (Test.run facts).code = 0 ↔ Test.Complete facts := by
  simp only [Test.run, Test.code_eq_zero_iff, Test.failuresOf_eq_empty_iff]

theorem Test.run_code_ne_zero_iff (facts : TestFacts) :
    (Test.run facts).code ≠ 0 ↔ (Test.run facts).failures ≠ #[] := by
  simp only [Test.run, ne_eq, Test.code_eq_zero_iff]

private def passingTests : TestFacts :=
  { declaredChecks := #[], checks := #[], declaredOwnTests := #[], ownTests := #[], unknownOwnTests := #[],
    testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, libraryPlace := ⟨"lakefile.lean", 1⟩ }

private def unknownTest : TestFacts := { passingTests with unknownOwnTests := #["own"] }

private theorem passingTests_complete : Test.Complete passingTests where
  checksRun := by simp [passingTests]
  checksPass := by simp [passingTests]
  ownTestsRun := by simp [passingTests]
  ownTestsPass := by simp [passingTests]
  ownTestsDeclared := rfl

theorem Test.run_code_eq_zero_iff_rejects_accepting :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 0 } : Test.Result)) facts).code = 0 ↔
        Test.Complete facts := fun holds => by
  have declared := ((holds unknownTest).mp rfl).ownTestsDeclared
  simp [unknownTest] at declared

theorem Test.run_code_eq_zero_iff_rejects_refusing :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 1 } : Test.Result)) facts).code = 0 ↔
        Test.Complete facts := fun holds =>
  absurd ((holds passingTests).mpr passingTests_complete) (by decide)

theorem Test.run_code_ne_zero_iff_rejects_accepting :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) =>
        ({ failures := #[.unknownOwnTest "own" ⟨"lakefile.lean", 1⟩], timings := #[], code := 0 } :
          Test.Result)) facts).code ≠ 0 ↔
        ((fun (_ : TestFacts) =>
          ({ failures := #[.unknownOwnTest "own" ⟨"lakefile.lean", 1⟩], timings := #[], code := 0 } :
            Test.Result)) facts).failures ≠ #[] := fun holds =>
  (holds default).mpr (by simp) rfl

theorem Test.run_code_ne_zero_iff_rejects_refusing :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 1 } : Test.Result)) facts).code ≠ 0 ↔
        ((fun (_ : TestFacts) =>
          ({ failures := #[], timings := #[], code := 1 } : Test.Result)) facts).failures ≠ #[] := fun holds =>
  (holds default).mp (by decide) rfl

end SoftwareChallenge

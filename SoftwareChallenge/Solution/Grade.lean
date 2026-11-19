module

public import SoftwareChallenge.CoreCode.Grade
import all SoftwareChallenge.CoreCode.Grade

public section

namespace SoftwareChallenge

theorem Grade.decide_eq_accept_iff (observations : List Observation) :
    Grade.decide observations = .accept ↔
      observations.map (·.stage) = Stage.order ∧ ∀ observation ∈ observations, observation.verdict = .accept := by
  unfold Grade.decide
  split
  · rename_i stopped found
    have refused : stopped.verdict ≠ .accept := by simpa using List.find?_some found
    refine ⟨fun accepted => absurd accepted refused, fun ⟨_, accepted⟩ => ?_⟩
    exact absurd (accepted stopped (List.mem_of_find?_eq_some found)) refused
  · rename_i none
    have accepted : ∀ observation ∈ observations, observation.verdict = .accept := by
      simpa using List.find?_eq_none.mp none
    split <;> simp_all

theorem Grade.decide_eq_accept_iff_rejects_accepting :
    ¬ ∀ (observations : List Observation),
      (fun (_ : List Observation) => Verdict.accept) observations = .accept ↔
      observations.map (·.stage) = Stage.order ∧ ∀ observation ∈ observations, observation.verdict = .accept := by
  intro accepts
  have ordered := ((accepts []).mp rfl).1
  simp [Stage.order] at ordered

theorem Grade.decide_eq_first (passed : List Observation) (stopped : Observation) (rest : List Observation)
    (allPassed : ∀ observation ∈ passed, observation.verdict = .accept) (failed : stopped.verdict ≠ .accept) :
    Grade.decide (passed ++ stopped :: rest) = stopped.verdict := by
  have skipped : passed.find? (·.verdict != .accept) = none :=
    List.find?_eq_none.mpr fun observation member => by simp [allPassed observation member]
  have found : (passed ++ stopped :: rest).find? (·.verdict != .accept) = some stopped := by
    rw [List.find?_append, skipped]
    simp [failed]
  simp [Grade.decide, found]

theorem Grade.decide_eq_first_rejects_refusing :
    ¬ ∀ (passed : List Observation) (stopped : Observation) (rest : List Observation),
      (∀ observation ∈ passed, observation.verdict = .accept) → stopped.verdict ≠ .accept →
      (fun (_ : List Observation) => Verdict.refuse) (passed ++ stopped :: rest) = stopped.verdict := by
  intro refuses
  have judged := refuses [] { stage := .lock, verdict := .cannotJudge, detail := "" } [] (by simp) (by decide)
  simp at judged

end SoftwareChallenge

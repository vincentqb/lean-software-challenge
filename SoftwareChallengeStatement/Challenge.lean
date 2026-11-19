module

public import SoftwareChallenge.CoreSpec.Package
public import SoftwareChallenge.CoreSpec.Shape
public import SoftwareChallenge.CoreSpec.Expr
public import SoftwareChallenge.CoreSpec.Graph
public import SoftwareChallenge.CoreSpec.Format
public import SoftwareChallenge.CoreSpec.Grade
public import SoftwareChallenge.CoreSpec.Lint
public import SoftwareChallenge.CoreSpec.Test
meta import SoftwareChallenge

public section

/-!
# Lean Software Challenge, judged by itself

Not claimed:
- that the reader's facts, binder shapes included, match Lean, Lake, or the files;
- that a message's fix works;
- that each message names a condition the facts miss;
- that lint exits 2, rather than another code, when only pending items remain;
- that Lake reads a plain name back as `Config.parse` does;
- that `lake comparator` judges as the comparator model says;
- that each derived witness quantifies the binders Telescope.kept chooses.
-/

namespace SoftwareChallenge

open Lean

def Project.violations : Project → Inventory → Array Violation := sorry

def Shape.witnesses? : (Name → Bool) → Shape → Shape → Option Witnesses := sorry

def Shape.isKill : (Name → Bool) → Shape → Shape → Bool := sorry

def Shape.independent : (Name → Bool) → Shape → List Shape → Shape → Bool := sorry

def Shape.ofExpr : Expr → Shape := sorry

def Graph.closure : Graph → Array Name → Std.HashSet Name := sorry

def Config.render : Config → String := sorry

def Config.parse : String → Option Config := sorry

def Lock.render : Array Lock.Entry → String := sorry

def Lock.parse : String → Option (Array Lock.Entry) := sorry

def Lock.violations : Array Lock.Entry → Array Lock.Entry → Array Lock.Violation := sorry

def Grade.decide : List Observation → Verdict := sorry

def Statement.run : LakeFacts → FileFacts → ChallengeFacts → Statement.Result := sorry

def Lint.run : Facts → Lint.Result := sorry

def Test.run : TestFacts → Test.Result := sorry

theorem layering_sound (project : Project) (inventory : Inventory)
    (accepted : project.violations inventory = #[]) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  sorry

@[kills layering_sound] theorem layering_sound_rejects_accepting :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => (#[] : Array Violation)) project inventory = #[] →
      ∀ (source target : Name) (role : Role), project.role? source = some role → role.Inner →
      Relation.TransGen inventory.RuntimeImport source target →
      ∀ reached, project.role? target = some reached → reached.Inner := by
  sorry

theorem purity_sound (project : Project) (inventory : Inventory)
    (accepted : project.violations inventory = #[]) (fact : DeclarationFact)
    (listed : fact ∈ inventory.declarations) :
    ∃ role, project.role? fact.module = some role ∧ (∀ used ∈ fact.axioms, used ∈ standardAxioms) ∧
      (fact.computational = true → fact.Allowed role) := by
  sorry

@[kills purity_sound] theorem purity_sound_rejects_accepting :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => (#[] : Array Violation)) project inventory = #[] →
      ∀ (fact : DeclarationFact), fact ∈ inventory.declarations →
      ∃ role, project.role? fact.module = some role ∧ (∀ used ∈ fact.axioms, used ∈ standardAxioms) ∧
        (fact.computational = true → fact.Allowed role) := by
  sorry

theorem Project.violations_eq_empty_iff_admits (project : Project) (inventory : Inventory) :
    project.violations inventory = #[] ↔ project.Admits inventory := by
  sorry

@[kills Project.violations_eq_empty_iff_admits]
theorem Project.violations_eq_empty_iff_admits_rejects_accepting :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => (#[] : Array Violation)) project inventory = #[] ↔
        project.Admits inventory := by
  sorry

@[kills Project.violations_eq_empty_iff_admits]
theorem Project.violations_eq_empty_iff_admits_rejects_refusing :
    ¬ ∀ (project : Project) (inventory : Inventory),
      (fun (_ : Project) (_ : Inventory) => #[Violation.unplaced .anonymous]) project inventory = #[] ↔
        project.Admits inventory := by
  sorry

theorem Shape.witnesses?_sound {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (found : pattern.witnesses? replaceable target = some σ) :
    (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  sorry

@[kills Shape.witnesses?_sound] theorem Shape.witnesses?_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses},
      (fun (_ : Name → Bool) (_ _ : Shape) => (some [] : Option Witnesses)) replaceable pattern target = some σ →
      (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  sorry

theorem Shape.witnesses?_complete {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true)
    (instantiates : pattern.subst replaceable σ = target) :
    (pattern.witnesses? replaceable target).isSome := by
  sorry

@[kills Shape.witnesses?_complete] theorem Shape.witnesses?_complete_rejects_refusing :
    ¬ ∀ {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses},
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) →
      pattern.subst replaceable σ = target →
      ((fun (_ : Name → Bool) (_ _ : Shape) => (none : Option Witnesses)) replaceable pattern target).isSome := by
  sorry

theorem Shape.isKill_sound {replaceable : Name → Bool} {headline kill : Shape}
    (accepted : headline.isKill replaceable kill = true) :
    ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
      kill = (headline.subst replaceable σ).negation := by
  sorry

@[kills Shape.isKill_sound] theorem Shape.isKill_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {headline kill : Shape},
      (fun (_ : Name → Bool) (_ _ : Shape) => true) replaceable headline kill = true →
      ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
        kill = (headline.subst replaceable σ).negation := by
  sorry

theorem Shape.isKill_complete {replaceable : Name → Bool} {headline : Shape} {σ : Witnesses}
    (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) :
    headline.isKill replaceable (headline.subst replaceable σ).negation = true := by
  sorry

@[kills Shape.isKill_complete] theorem Shape.isKill_complete_rejects_refusing :
    ¬ ∀ {replaceable : Name → Bool} {headline : Shape} {σ : Witnesses},
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) →
      (fun (_ : Name → Bool) (_ _ : Shape) => false) replaceable headline
        (headline.subst replaceable σ).negation = true := by
  sorry

theorem Shape.independent_sound {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape}
    (accepted : headline.independent replaceable others kill = true) :
    others ≠ [] ∧ ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
      kill = Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) := by
  sorry

@[kills Shape.independent_sound] theorem Shape.independent_sound_rejects_accepting :
    ¬ ∀ {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape},
      (fun (_ : Name → Bool) (_ : Shape) (_ : List Shape) (_ : Shape) => true) replaceable headline others kill = true →
      others ≠ [] ∧ ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧
        kill = Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) := by
  sorry

theorem Shape.independent_complete {replaceable : Name → Bool} {headline : Shape} {others : List Shape}
    {σ : Witnesses} (fixed : replaceable ``And = false ∧ replaceable ``Not = false ∧ replaceable ``True = false)
    (nonempty : others ≠ []) (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) :
    headline.independent replaceable others
      (Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ))) = true := by
  sorry

@[kills Shape.independent_complete] theorem Shape.independent_complete_rejects_refusing :
    ¬ ∀ {replaceable : Name → Bool} {headline : Shape} {others : List Shape} {σ : Witnesses},
      (replaceable ``And = false ∧ replaceable ``Not = false ∧ replaceable ``True = false) → others ≠ [] →
      (∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true) →
      (fun (_ : Name → Bool) (_ : Shape) (_ : List Shape) (_ : Shape) => false) replaceable headline others
        (Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ))) = true := by
  sorry

theorem Shape.ofExpr_eq_iff (left right : Expr) : Shape.ofExpr left = Shape.ofExpr right ↔ ExprSimilar left right := by
  sorry

@[kills Shape.ofExpr_eq_iff] theorem Shape.ofExpr_eq_iff_rejects_constant :
    ¬ ∀ (left right : Expr),
      (fun (_ : Expr) => Shape.natLit 0) left = (fun (_ : Expr) => Shape.natLit 0) right ↔ ExprSimilar left right := by
  sorry

theorem Graph.closure_sound (graph : Graph) (roots : Array Name) (node : Name)
    (member : node ∈ graph.closure roots) : ∃ root ∈ roots, graph.Reaches root node := by
  sorry

@[kills Graph.closure_sound] theorem Graph.closure_sound_rejects_extra_node :
    ¬ ∀ (graph : Graph) (roots : Array Name) (node : Name),
      node ∈ (fun (_ : Graph) (roots : Array Name) => Std.HashSet.ofList (roots.push `extra).toList) graph roots →
      ∃ root ∈ roots, graph.Reaches root node := by
  sorry

theorem Graph.closure_complete (graph : Graph) (roots : Array Name) (root node : Name) (rooted : root ∈ roots)
    (path : graph.Reaches root node) : node ∈ graph.closure roots := by
  sorry

@[kills Graph.closure_complete] theorem Graph.closure_complete_rejects_roots_only :
    ¬ ∀ (graph : Graph) (roots : Array Name) (root node : Name), root ∈ roots → graph.Reaches root node →
      node ∈ (fun (_ : Graph) (roots : Array Name) => Std.HashSet.ofList roots.toList) graph roots := by
  sorry

theorem Config.parse_render (config : Config) (plain : config.Plain) :
    Config.parse (Config.render config) = some config := by
  sorry

@[kills Config.parse_render] theorem Config.parse_render_rejects_refusing :
    ¬ ∀ (config : Config), config.Plain →
      (fun (_ : String) => (none : Option Config)) (Config.render config) = some config := by
  sorry

theorem Lock.parse_render (entries : Array Lock.Entry) : Lock.parse (Lock.render entries) = some entries := by
  sorry

@[kills Lock.parse_render] theorem Lock.parse_render_rejects_refusing :
    ¬ ∀ (entries : Array Lock.Entry),
      (fun (_ : String) => (none : Option (Array Lock.Entry))) (Lock.render entries) = some entries := by
  sorry

theorem Lock.violations_eq_empty_iff (locked current : Array Lock.Entry) :
    Lock.violations locked current = #[] ↔ ∀ path, Lock.digestOf locked path = Lock.digestOf current path := by
  sorry

@[kills Lock.violations_eq_empty_iff] theorem Lock.violations_eq_empty_iff_rejects_accepting :
    ¬ ∀ (locked current : Array Lock.Entry),
      (fun (_ _ : Array Lock.Entry) => (#[] : Array Lock.Violation)) locked current = #[] ↔
      ∀ path, Lock.digestOf locked path = Lock.digestOf current path := by
  sorry

theorem Grade.decide_eq_accept_iff (observations : List Observation) :
    Grade.decide observations = .accept ↔
      observations.map (·.stage) = Stage.order ∧ ∀ observation ∈ observations, observation.verdict = .accept := by
  sorry

@[kills Grade.decide_eq_accept_iff] theorem Grade.decide_eq_accept_iff_rejects_accepting :
    ¬ ∀ (observations : List Observation),
      (fun (_ : List Observation) => Verdict.accept) observations = .accept ↔
      observations.map (·.stage) = Stage.order ∧ ∀ observation ∈ observations, observation.verdict = .accept := by
  sorry

theorem Grade.decide_eq_first (passed : List Observation) (stopped : Observation) (rest : List Observation)
    (allPassed : ∀ observation ∈ passed, observation.verdict = .accept) (failed : stopped.verdict ≠ .accept) :
    Grade.decide (passed ++ stopped :: rest) = stopped.verdict := by
  sorry

@[kills Grade.decide_eq_first] theorem Grade.decide_eq_first_rejects_refusing :
    ¬ ∀ (passed : List Observation) (stopped : Observation) (rest : List Observation),
      (∀ observation ∈ passed, observation.verdict = .accept) → stopped.verdict ≠ .accept →
      (fun (_ : List Observation) => Verdict.refuse) (passed ++ stopped :: rest) = stopped.verdict := by
  sorry

theorem Statement.run_code_eq_zero_iff (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) :
    (Statement.run lake files challenge).code = 0 ↔ Statement.Complete lake files challenge := by
  sorry

@[kills Statement.run_code_eq_zero_iff] theorem Statement.run_code_eq_zero_iff_rejects_accepting :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 0 } :
          Statement.Result)) lake files challenge).code = 0 ↔ Statement.Complete lake files challenge := by
  sorry

@[kills Statement.run_code_eq_zero_iff] theorem Statement.run_code_eq_zero_iff_rejects_refusing :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
          Statement.Result)) lake files challenge).code = 0 ↔ Statement.Complete lake files challenge := by
  sorry

theorem Statement.run_code_ne_zero_iff (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) :
    (Statement.run lake files challenge).code ≠ 0 ↔
      (Statement.run lake files challenge).setup ≠ #[] ∨ (Statement.run lake files challenge).errors ≠ #[] := by
  sorry

@[kills Statement.run_code_ne_zero_iff] theorem Statement.run_code_ne_zero_iff_rejects_accepting :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[.noStatementTarget], writes := { lock? := none, config? := none },
           code := 0 } : Statement.Result)) lake files challenge).code ≠ 0 ↔
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[.noStatementTarget], writes := { lock? := none, config? := none },
             code := 0 } : Statement.Result)) lake files challenge).setup ≠ #[] ∨
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[.noStatementTarget], writes := { lock? := none, config? := none },
             code := 0 } : Statement.Result)) lake files challenge).errors ≠ #[] := by
  sorry

@[kills Statement.run_code_ne_zero_iff] theorem Statement.run_code_ne_zero_iff_rejects_refusing :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
          Statement.Result)) lake files challenge).code ≠ 0 ↔
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
            Statement.Result)) lake files challenge).setup ≠ #[] ∨
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
            Statement.Result)) lake files challenge).errors ≠ #[] := by
  sorry

theorem Lint.run_code_eq_zero_iff (facts : Facts) : (Lint.run facts).code = 0 ↔ Lint.Complete facts := by
  sorry

@[kills Lint.run_code_eq_zero_iff] theorem Lint.run_code_eq_zero_iff_rejects_accepting :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 0 } : Lint.Result))
        facts).code = 0 ↔ Lint.Complete facts := by
  sorry

@[kills Lint.run_code_eq_zero_iff] theorem Lint.run_code_eq_zero_iff_rejects_refusing :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
        facts).code = 0 ↔ Lint.Complete facts := by
  sorry

theorem Lint.run_code_ne_one_iff (facts : Facts) : (Lint.run facts).code ≠ 1 ↔ Lint.Clean facts := by
  sorry

@[kills Lint.run_code_ne_one_iff] theorem Lint.run_code_ne_one_iff_rejects_accepting :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 0 } : Lint.Result))
        facts).code ≠ 1 ↔ Lint.Clean facts := by
  sorry

@[kills Lint.run_code_ne_one_iff] theorem Lint.run_code_ne_one_iff_rejects_refusing :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
        facts).code ≠ 1 ↔ Lint.Clean facts := by
  sorry

theorem Lint.run_code_ne_zero_iff (facts : Facts) :
    (Lint.run facts).code ≠ 0 ↔ (Lint.run facts).errors ≠ #[] ∨ (Lint.run facts).pending ≠ #[] := by
  sorry

@[kills Lint.run_code_ne_zero_iff] theorem Lint.run_code_ne_zero_iff_rejects_accepting :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) =>
        ({ errors := #[.noStatementTarget], pending := #[], report := #[], code := 0 } : Lint.Result))
          facts).code ≠ 0 ↔
        ((fun (_ : Facts) =>
          ({ errors := #[.noStatementTarget], pending := #[], report := #[], code := 0 } : Lint.Result))
            facts).errors ≠ #[] ∨
        ((fun (_ : Facts) =>
          ({ errors := #[.noStatementTarget], pending := #[], report := #[], code := 0 } : Lint.Result))
            facts).pending ≠ #[] := by
  sorry

@[kills Lint.run_code_ne_zero_iff] theorem Lint.run_code_ne_zero_iff_rejects_refusing :
    ¬ ∀ (facts : Facts),
      ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
        facts).code ≠ 0 ↔
        ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
          facts).errors ≠ #[] ∨
        ((fun (_ : Facts) => ({ errors := #[], pending := #[], report := #[], code := 1 } : Lint.Result))
          facts).pending ≠ #[] := by
  sorry

theorem Test.run_code_eq_zero_iff (facts : TestFacts) : (Test.run facts).code = 0 ↔ Test.Complete facts := by
  sorry

@[kills Test.run_code_eq_zero_iff] theorem Test.run_code_eq_zero_iff_rejects_accepting :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 0 } : Test.Result)) facts).code = 0 ↔
        Test.Complete facts := by
  sorry

@[kills Test.run_code_eq_zero_iff] theorem Test.run_code_eq_zero_iff_rejects_refusing :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 1 } : Test.Result)) facts).code = 0 ↔
        Test.Complete facts := by
  sorry

theorem Test.run_code_le_two (facts : TestFacts) : (Test.run facts).code ≤ 2 := by
  sorry

@[kills Test.run_code_le_two] theorem Test.run_code_le_two_rejects_unjudged :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 3 } : Test.Result)) facts).code ≤ 2 := by
  sorry

theorem Test.run_code_ne_zero_iff (facts : TestFacts) :
    (Test.run facts).code ≠ 0 ↔ (Test.run facts).failures ≠ #[] := by
  sorry

@[kills Test.run_code_ne_zero_iff] theorem Test.run_code_ne_zero_iff_rejects_accepting :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) =>
        ({ failures := #[.unknownOwnTest "own" ⟨"lakefile.lean", 1⟩], timings := #[], code := 0 } :
          Test.Result)) facts).code ≠ 0 ↔
        ((fun (_ : TestFacts) =>
          ({ failures := #[.unknownOwnTest "own" ⟨"lakefile.lean", 1⟩], timings := #[], code := 0 } :
            Test.Result)) facts).failures ≠ #[] := by
  sorry

@[kills Test.run_code_ne_zero_iff] theorem Test.run_code_ne_zero_iff_rejects_refusing :
    ¬ ∀ (facts : TestFacts),
      ((fun (_ : TestFacts) => ({ failures := #[], timings := #[], code := 1 } : Test.Result)) facts).code ≠ 0 ↔
        ((fun (_ : TestFacts) =>
          ({ failures := #[], timings := #[], code := 1 } : Test.Result)) facts).failures ≠ #[] := by
  sorry

end SoftwareChallenge

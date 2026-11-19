module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Solution

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def standing (name : Name) : Name := fixture (`Standing ++ name)

def foundNamed (solution : SolutionFacts) (name : Name) : IO FoundFact :=
  match solution.found.find? (·.constant.name == name) with
  | some found => pure found
  | none => throw <| .userError s!"{name} was not found in the solution"

def targetNamed (challenge : ChallengeFacts) (name : Name) : IO TargetFact :=
  match challenge.targets.find? (·.constant.name == name) with
  | some target => pure target
  | none => throw <| .userError s!"{name} is not a target of {challenge.module}"

run_cmd Elab.Command.liftCoreM do
  let modules := #[`CoreSpec, `WorldSpec, `Standing.Solution, `Standing.Outside].map fixture
  let lake ← lakeOf modules (some (fixture `Standing.Challenge))
  let challenge ← readChallenge lake .lint
  let solution ← readSolution lake challenge .lint
  check (solution.solution? == some (standing `Solution)) "the Solution module was not found"
  check (solution.solutionClosure.contains (standing `Solution) &&
      solution.solutionClosure.contains (fixture `WorldSpec) &&
      !solution.solutionClosure.contains (standing `Outside)) "the Solution import closure was misread"
  check (solution.importsSolution == #[standing `Outside]) "the modules that import Solution were misread"
  for name in [`zero_right, `zero_implicit, `hole, `zero_unsound] do
    let target ← targetNamed challenge (standing name)
    let found ← foundNamed solution (standing name)
    check (found.constant.type == target.constant.type && found.constant.kind == target.constant.kind &&
        found.constant.levels == target.constant.levels && found.module == standing `Solution)
      s!"{name}, which the solution restates up to binder names and kinds, was read otherwise"
  check ((← foundNamed solution (standing `zero_kind)).constant.kind == .defined .safe)
    "a def restating a theorem was misread"
  check ((← foundNamed solution (standing `in_u)).constant.levels == [`v] &&
      (← targetNamed challenge (standing `in_u)).constant.levels == [`u]) "universe parameters were misread"
  let flipped ← foundNamed solution (standing `zero_flipped)
  check (flipped.constant.type != (← targetNamed challenge (standing `zero_flipped)).constant.type &&
      flipped.rendered == "∀ (n : Nat), n = n + 0" && flipped.place.line == 22 &&
      flipped.place.file == "SoftwareChallengeTests/Fixtures/Standing/Solution.lean")
    s!"a restatement that differs was misread: {flipped.rendered} at line {flipped.place.line}"
  check (!solution.found.any (·.constant.name == standing `zero_absent)) "an absent theorem was found"
  check ((← foundNamed solution (standing `zero_outside)).module == standing `Outside)
    "a theorem outside the Solution's imports was misread"
  check ((declarationNamed? solution.inventory (standing `Solution) (standing `zero_unsound)).any
      (·.axioms.contains ``sorryAx)) "a proof that uses sorry was not read as unsound"
  let first ← targetNamed challenge (standing `first_is_zero)
  check (!first.auxiliaries.isEmpty && first.auxiliaries.all fun auxiliary =>
      !solution.found.any (·.constant.name == auxiliary.name)) "an auxiliary no solution reproduces was found"
  check ((← foundNamed solution (standing `hole)).compiled && !(← foundNamed solution (standing `hole_lost)).compiled)
    "whether a hole is computable was misread"
  check (solution.found.all fun found => found.constant.kind != .proved || found.constant.value?.isSome)
    "a proof the solution states was not readable"
  check (solution.premiseUses.find? (·.1 == standing `succ_positive) == some (standing `succ_positive, #[1]) &&
      solution.premiseUses.find? (·.1 == standing `succ_correct) == some (standing `succ_correct, #[0, 1]))
    s!"the binders a proof uses were misread: {solution.premiseUses}"

run_cmd Elab.Command.liftCoreM do
  let modules := #[`CoreSpec, `WorldSpec, `CoreCode, `WorldCode, `Sibling, `Program].map fixture
  let lake ← lakeOf modules (some (fixture `ClaimChallenge))
  let challenge ← readChallenge lake .lint
  let imported ← catalogEnv lake challenge.module .lint
  let env := imported.env
  let catalogModules ← catalogModules lake (catalog lake challenge.module) imported .lint
  let evidence ← runIn env (catalogEvidence catalogModules)
  let uses ← runIn env (claimUses challenge evidence (budget := 2000))
  let member := fun (name : Name) => fixture (`ClaimChallenge ++ name)
  let outcomes := fun (headline : Name) => ((uses.find? (·.headline == member headline)).map fun use =>
    use.checks.map fun (check, outcome) => (check.place.file, check.place.line, outcome)).getD #[]
  let worldCode := "SoftwareChallengeTests/Fixtures/WorldCode.lean"
  let sibling := "SoftwareChallengeTests/Fixtures/Sibling.lean"
  check (outcomes `bump_grows == #[(worldCode, 39, .matched), (sibling, 10, .matched), (sibling, 12, .differs)])
    s!"the Checks of SuccAgrees nativeSucc were misjudged: {repr (outcomes `bump_grows)}"
  check (outcomes `bump_on_positives == #[(worldCode, 52, .matched)])
    "a Check of a world claim under ∀ and → was not matched against its peeled conclusion"
  check (outcomes `bump_at_leaves == #[(worldCode, 52, .undecided)])
    "a Check that cannot be matched within the budget was decided"
  check (outcomes `bump_wrapped == outcomes `bump_grows) "a world claim a WorldSpec definition wraps was misjudged"
  check ((uses.find? (·.headline == member `bump_unchecked)).any fun use => use.claim == fixture `Unchecked &&
      use.checks.isEmpty && use.binder == 0) "an unchecked world claim was misread"
  check (uses.all fun use => use.statement == ((challenge.headlines.find? (·.target.constant.name == use.headline)).bind
      fun headline => (headline.claims.find? (·.1 == use.binder)).map (·.2.2)).getD "")
    "a claim use does not carry its headline's statement of the claim"
  check ((evidence.filter (·.2.claim == fixture `WrongSuccAgrees)).size == 3)
    "the Checks of the catalog were misread"
  let solution ← readSolution lake (← challengeNamed (fixture `Challenge)) .lint
  check (solution.main? == some (fixture `Program, ⟨"SoftwareChallengeTests/Fixtures/Program.lean", 7⟩))
    s!"main was misread: {repr solution.main?}"
  check (solution.checks.any fun check => check.claim == fixture `SuccAt && check.statement ==
      "SoftwareChallengeTests.Fixtures.SuccAt 0" && check.place == { file := worldCode, line := 52 })
    "a Check's statement or place was misread"
  let marked ← runIn env do
    let some marked := (← getEnv).find? (fixture `identity_twice_rejects_marked) | throwError "a fixture is missing"
    let some plain := (← getEnv).find? (fixture `identity_twice_rejects_successor) | throwError "a fixture is missing"
    return (marked.type != plain.type, (constantFact marked).type == (constantFact plain).type)
  check (marked == (true, true)) "a statement's metadata was not dropped from its shape"
  let withoutIdentity := { solution.inventory with
    declarations := solution.inventory.declarations.filter (·.name != fixture `identity) }
  check (catalogMisses imported (catalog lake challenge.module) { solution with inventory := withoutIdentity } ==
      #[(fixture `CoreCode, fixture `identity)]) "the census missed a declaration the facts drop"
  let withoutSibling := { solution.inventory with
    modules := solution.inventory.modules.filter (·.name != fixture `Sibling) }
  check ((catalogMisses imported (catalog lake challenge.module) { solution with inventory := withoutSibling }).contains
      (fixture `Sibling, .anonymous)) "the census missed a module the facts drop"

end

end SoftwareChallengeReadTests.Solution

module

meta import Lean
meta import SoftwareChallengeTests.Model
meta import SoftwareChallengeTests.Golden.ConstantFolding

namespace SoftwareChallengeTests.Matrix

open Lean Elab Command SoftwareChallenge SoftwareChallengeTests.Model

meta section

def golden : Facts := SoftwareChallengeTests.Golden.constantFolding

def templateLibrary : Place := { file := "lakefile.lean", line := 17 }

def folding (last : String) : Name := .str `ConstantFolding last

def expect (found : Bool) (problem : String) : Except String Unit :=
  unless found do throw problem

def edited (path : String) (facts : Facts) : Except String Facts := do
  expect (facts.files.digests.any (·.path == path)) s!"{path} has no digest in the golden's files"
  return { facts with files := { facts.files with digests := facts.files.digests.map fun entry =>
    if entry.path == path then { entry with digest := entry.digest ++ "-edited" } else entry } }

def digested (path : String) (facts : Facts) : Facts :=
  { facts with files := { facts.files with digests := facts.files.digests.push { path, digest := s!"{path}-new" } } }

def mapHeadline (name : Name) (change : HeadlineFact → Except String HeadlineFact) (facts : Facts) :
    Except String Facts := do
  expect (facts.challenge.headlines.any (·.target.constant.name == name)) s!"the golden has no headline {name}"
  let headlines ← facts.challenge.headlines.mapM fun headline =>
    if headline.target.constant.name == name then change headline else pure headline
  return { facts with challenge := { facts.challenge with headlines } }

def mapKill (name : Name) (change : TargetFact → Except String TargetFact) (facts : Facts) :
    Except String Facts := do
  expect (facts.challenge.kills.any (·.target.constant.name == name)) s!"the golden has no kill {name}"
  let kills ← facts.challenge.kills.mapM fun kill =>
    if kill.target.constant.name == name then return { kill with target := (← change kill.target) } else pure kill
  return { facts with challenge := { facts.challenge with kills } }

def dropKill (name : Name) (facts : Facts) : Except String Facts := do
  expect (facts.challenge.kills.any (·.target.constant.name == name)) s!"the golden has no kill {name}"
  return { facts with challenge := { facts.challenge with
    kills := facts.challenge.kills.filter (·.target.constant.name != name) } }

def addHeadline (headline : HeadlineFact) (facts : Facts) : Facts :=
  { facts with challenge := { facts.challenge with headlines := facts.challenge.headlines.push headline } }

def mapFound (name : Name) (change : FoundFact → Except String FoundFact) (facts : Facts) :
    Except String Facts := do
  expect (facts.solution.found.any (·.constant.name == name)) s!"the golden's solution has no {name}"
  let found ← facts.solution.found.mapM fun found => if found.constant.name == name then change found else pure found
  return { facts with solution := { facts.solution with found } }

def dropFound (name : Name) (facts : Facts) : Except String Facts := do
  expect (facts.solution.found.any (·.constant.name == name)) s!"the golden's solution has no {name}"
  let found := facts.solution.found.filter (·.constant.name != name)
  return { facts with solution := { facts.solution with found } }

def declaration (name module : Name) (line : Nat) (computational : Bool) : DeclarationFact :=
  { name, module, line, computational, isUnsafe := false, isPartial := false, external := false, unfoldable := true,
    replaced := false, initializes := false, effects := false, debug := false, axioms := #[] }

def placed (fact : DeclarationFact) (file : String) : DeclarationPlace :=
  { name := fact.name, place := { file, line := fact.line }, written := fact.name.getString!,
    firstLine := s!"def {fact.name.getString!}" }

def declare (fact : DeclarationFact) (file : String) (facts : Facts) : Facts :=
  { facts with solution := { facts.solution with
    inventory := { facts.solution.inventory with declarations := facts.solution.inventory.declarations.push fact }
    places := facts.solution.places.push (placed fact file) } }

def declareOwned (fact : DeclarationFact) (file : String) (facts : Facts) : Facts :=
  let owned := facts.challenge.owned
  { facts with challenge := { facts.challenge with owned := { owned with
    inventory := { owned.inventory with declarations := owned.inventory.declarations.push fact }
    places := owned.places.push (placed fact file) } } }

def mapDeclaration (name : Name) (change : DeclarationFact → DeclarationFact) (facts : Facts) :
    Except String Facts := do
  let declarations := facts.solution.inventory.declarations
  expect (declarations.any (·.name == name)) s!"the golden's inventory has no {name}"
  return { facts with solution := { facts.solution with inventory := { facts.solution.inventory with
    declarations := declarations.map fun fact => if fact.name == name then change fact else fact } } }

def dropDeclaration (name : Name) (facts : Facts) : Except String Facts := do
  let declarations := facts.solution.inventory.declarations
  expect (declarations.any (·.name == name)) s!"the golden's inventory has no {name}"
  return { facts with solution := { facts.solution with inventory := { facts.solution.inventory with
    declarations := declarations.filter (·.name != name) } } }

def addModule (module : Name) (file : String) (imports : Array ImportFact) (facts : Facts) : Facts :=
  let fact : ModuleFact := { name := module, file, usesModuleSystem := true, imports }
  { facts with
    lake := { facts.lake with modules := facts.lake.modules.push { module, file } }
    solution := { facts.solution with
      inventory := { facts.solution.inventory with modules := facts.solution.inventory.modules.push fact }
      linted := facts.solution.linted.push module } }

def swapEquality : Shape → Option Shape
  | .app (.app (.app (.const name levels) type) left) right =>
    if name == ``Eq then some (.app (.app (.app (.const name levels) type) right) left) else none
  | _ => none

def atConclusion (change : Shape → Option Shape) : Shape → Option Shape
  | .forallE type body => (atConclusion change body).map (.forallE type)
  | shape => change shape

def underNegation (change : Shape → Option Shape) : Shape → Option Shape
  | .app (.const name levels) statement =>
    if name == ``Not then (change statement).map (.app (.const name levels)) else none
  | _ => none

def lift (cutoff : Nat) : Shape → Shape
  | .bvar index => .bvar (if index < cutoff then index else index + 1)
  | .app function argument => .app (lift cutoff function) (lift cutoff argument)
  | .lam type body => .lam (lift cutoff type) (lift (cutoff + 1) body)
  | .forallE type body => .forallE (lift cutoff type) (lift (cutoff + 1) body)
  | .letE type value body => .letE (lift cutoff type) (lift cutoff value) (lift (cutoff + 1) body)
  | .proj name index value => .proj name index (lift cutoff value)
  | shape => shape

def normalOfFirst : Shape :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
    (.app (.const (folding "normal") []) (.bvar 0))) (.const ``Bool.true [])

def assumingNormal : Shape → Option Shape
  | .forallE type body => some (.forallE type (.forallE normalOfFirst (lift 0 body)))
  | _ => none

def reshaped (change : Shape → Option Shape) (constant : ConstantFact) : Except String ConstantFact :=
  match change constant.type with
  | some type => pure { constant with type }
  | none => throw s!"{constant.name}: its type in the golden does not have the form the mutation rewrites"

def retarget (change : Shape → Option Shape) (text : String → String) (target : TargetFact) :
    Except String TargetFact := do
  return { target with
    constant := (← reshaped change target.constant), signature := text target.signature,
    rendered := text target.rendered, renderedExplicit := text target.renderedExplicit }

def refound (change : Shape → Option Shape) (text : String → String) (found : FoundFact) :
    Except String FoundFact := do
  return { found with
    constant := (← reshaped change found.constant), rendered := text found.rendered,
    renderedExplicit := text found.renderedExplicit }

def swappedText (text : String) : String :=
  ((text.replace "→ m = n" "→ n = m").replace ": m = n" ": n = m").replace "Nat m n" "Nat n m"

def weakenedText (text : String) : String :=
  (text.replace "(e : Expr) :" "(e : Expr) (_ : normal e = true) :").replace "(e : ConstantFolding.Expr), "
    "(e : ConstantFolding.Expr), ConstantFolding.normal e = true → "

def keepsLiteral : Name := folding "fold_keeps_literal"

def keepsLiteralKill : Name := folding "fold_keeps_literal_rejects_zero"

def idempotent : Name := folding "fold_idempotent"

def idempotentKill : Name := folding "fold_idempotent_rejects_increment"

def normalizesKill : Name := folding "fold_normalizes_rejects_identity"

def restatedByOwner (facts : Facts) : Except String Facts := do
  let facts ← mapHeadline keepsLiteral (fun headline => do
    return { headline with target := (← retarget (atConclusion swapEquality) swappedText headline.target),
                           killTemplate? := headline.killTemplate?.map swappedText }) facts
  let facts ← mapKill keepsLiteralKill (retarget (underNegation (atConclusion swapEquality)) swappedText) facts
  edited "Challenge.lean" facts

def restatedByAgent (facts : Facts) : Except String Facts := do
  let facts ← mapFound keepsLiteral (refound (atConclusion swapEquality) swappedText) facts
  mapFound keepsLiteralKill (refound (underNegation (atConclusion swapEquality)) swappedText) facts

def normalBinder : BinderFact :=
  { name := "x", type := normalOfFirst, meaning := normalOfFirst, prop := true, shown := "normal e = true",
    conclusion := "normal e = true", variables := #["e"] }

def weakenedByOwner (facts : Facts) : Except String Facts := do
  let facts ← mapHeadline idempotent (fun headline => do
    return { headline with target := (← retarget assumingNormal weakenedText headline.target),
                           telescope := headline.telescope ++ [normalBinder] }) facts
  let facts ← mapKill idempotentKill (retarget (underNegation assumingNormal) weakenedText) facts
  edited "Challenge.lean" facts

def weakenedSolution (facts : Facts) : Except String Facts :=
  mapFound idempotent (refound assumingNormal weakenedText) facts

def droppedKillProof (facts : Facts) : Except String Facts := do
  dropDeclaration normalizesKill (← dropFound normalizesKill facts)

def nativeMissing : String :=
  "Could not find native implementation of external declaration 'ConstantFolding.nativeAdd' (symbols \
    'l_ConstantFolding_nativeAdd___boxed' or 'l_ConstantFolding_nativeAdd')"

def failingFirstCheck (facts : TestFacts) : Except String TestFacts := do
  expect (!facts.checks.isEmpty) "the golden declares no Check"
  return { facts with checks := facts.checks.modify 0 ({ · with error? := some "nativeAdd 0 7 disagrees" }) }

def gradedHeadline : HeadlineFact :=
  { target := { constant := { name := `graded, kind := .proved, levels := [], type := .const ``True [],
                              value? := some (.const ``trivial []), hints := "", mutualBlock := [`graded],
                              isPrivate := false }
                place := { file := "Challenge.lean", line := 71 }, written := "graded",
                enclosingNamespace := .anonymous, signature := ": True", rendered := "True",
                renderedExplicit := "True", auxiliaries := #[] }
    telescope := [], killTemplate? := none, witness? := none }

def extraSpec : Name := `ConstantFolding.CoreSpec.Extra

def extraFile : String := "ConstantFolding/CoreSpec/Extra.lean"

def addsOwnedFile (facts : Facts) : Except String Facts := do
  let extra := declaration `ConstantFolding.extra extraSpec 5 false
  let facts := declare extra extraFile (addModule extraSpec extraFile #[{ name := `Init, comptime := false, line := 0 }]
    { facts with lake := { facts.lake with inputs := facts.lake.inputs.push extraFile } })
  return declareOwned extra extraFile (digested extraFile facts)

def provedOutside (facts : Facts) : Except String Facts := do
  let proofs : Name := `ConstantFolding.Proofs
  let facts ← mapFound idempotent (fun found => pure { found with
    module := proofs, place := { file := "ConstantFolding/Proofs.lean", line := 7 } }) facts
  let facts ← mapDeclaration idempotent ({ · with module := proofs, line := 7 }) facts
  let facts := addModule proofs "ConstantFolding/Proofs.lean"
    #[{ name := `Init, comptime := false, line := 0 },
      { name := `ConstantFolding.Solution, comptime := false, line := 3 }] facts
  let importsSolution := facts.solution.importsSolution.push proofs
  return { facts with solution := { facts.solution with importsSolution } }

def rows : List (Row × Cells) := [
  ({ name := "owner-unchanged" }, ⟨0, 0, 0, 0, 0⟩),
  ({ name := "owner-drops-kill",
     owner? := some fun facts => do edited "Challenge.lean" (← dropKill normalizesKill facts) },
    ⟨1, 1, 0, 0, 3⟩),
  ({ name := "owner-restates-headline", owner? := some restatedByOwner }, ⟨0, 2, 0, 1, 1⟩),
  ({ name := "owner-breaks-solution", owner? := some (edited "ConstantFolding/CoreSpec.lean"), compiles := false },
    ⟨1, 1, 1, 3, 1⟩),
  ({ name := "owner-io-in-corespec", owner? := some fun facts => do
      let announce := { declaration (folding "announce") `ConstantFolding.CoreSpec 32 true with effects := true }
      return declareOwned announce "ConstantFolding/CoreSpec.lean"
        (declare announce "ConstantFolding/CoreSpec.lean" (← edited "ConstantFolding/CoreSpec.lean" facts)) },
    ⟨1, 1, 0, 0, 3⟩),
  ({ name := "owner-drops-precompile", owner? := some (edited "lakefile.lean")
     tests := fun facts => pure { facts with checks := facts.checks.map ({ · with error? := some nativeMissing }) } },
    ⟨0, 0, 1, 0, 1⟩),
  ({ name := "owner-adds-failing-test", owner? := some fun facts => do
      let facts ← edited "lakefile.lean" facts
      return { facts with lake := { facts.lake with
        testDriverArgs := #["own_test"], testDriverArgsPlace := { file := "lakefile.lean", line := 7 },
        ownTests := #[{ name := "own_test", kind := .script, place := { file := "lakefile.lean", line := 34 } }] } }
     tests := fun facts => pure { facts with ownTests := facts.ownTests.map ({ · with code := 2 }) } },
    ⟨0, 0, 2, 0, 1⟩),
  ({ name := "owner-requires-hidden-dependency", owner? := some fun facts => do
      expect (!facts.lake.packages.isEmpty) "the golden requires no package"
      let facts ← edited "lakefile.lean" facts
      let packages := facts.lake.packages.map
        ({ · with configured := "/tmp/software_challenge", real := "/tmp/software_challenge" })
      return { facts with lake := { facts.lake with packages } } },
    ⟨0, 2, 0, 3, 3⟩),
  ({ name := "agent-proves-restated-headline", owner? := some restatedByOwner, agent := restatedByAgent },
    ⟨0, 0, 0, 0, 0⟩),
  ({ name := "agent-honest", agent := fun facts =>
      pure (declare (declaration (folding "fold_fold") `ConstantFolding.CoreCode 58 false)
        "ConstantFolding/CoreCode.lean" facts) }, ⟨0, 0, 0, 0, 0⟩),
  ({ name := "agent-implemented-by", agent := fun facts => do
      let facts ← mapDeclaration (folding "fold") ({ · with replaced := true }) facts
      return declare (declaration (folding "foldAtRuntime") `ConstantFolding.CoreCode 13 true)
        "ConstantFolding/CoreCode.lean" facts }, ⟨0, 1, 0, 0, 1⟩),
  ({ name := "agent-forges-proof", observed? := some .refuse, agent := fun facts => do
      let forged := declaration (folding "fold_forged") `ConstantFolding.Solution 21 false
      let facts := declare forged "ConstantFolding/Solution.lean" facts
      let proofUses := facts.solution.proofUses.map fun (user, used) =>
        if user == idempotent then (user, #[forged.name]) else (user, used)
      return { facts with solution := { facts.solution with proofUses } } }, ⟨0, 0, 0, 1, 1⟩),
  ({ name := "agent-drops-checks", agent := fun facts => do
      expect (!facts.solution.checks.isEmpty) "the golden declares no Check"
      let facts := declare { declaration (folding "probeAdd") `ConstantFolding.WorldCode 31 true with effects := true }
        "ConstantFolding/WorldCode.lean" facts
      return { facts with solution := { facts.solution with
        checks := #[], claimUses := facts.solution.claimUses.map ({ · with checks := #[] }) } } }, ⟨0, 2, 0, 0, 1⟩),
  ({ name := "agent-failing-check", tests := failingFirstCheck }, ⟨0, 0, 1, 0, 1⟩),
  ({ name := "agent-edits-challenge", agent := fun facts => do
      return addHeadline gradedHeadline (← edited "Challenge.lean" facts) }, ⟨1, 1, 0, 0, 1⟩),
  ({ name := "agent-adds-owned-file", agent := addsOwnedFile }, ⟨1, 1, 0, 0, 1⟩),
  ({ name := "agent-weakens-solution", agent := weakenedSolution }, ⟨0, 2, 0, 1, 1⟩),
  ({ name := "agent-drops-kill-proof", agent := droppedKillProof }, ⟨0, 2, 0, 1, 1⟩),
  ({ name := "agent-lint-warning-pending", agent := fun facts => do
      let facts := declare (declaration (folding "self_eq") `ConstantFolding.CoreCode 58 false)
        "ConstantFolding/CoreCode.lean" (← droppedKillProof facts)
      let warning : LintFact :=
        { module := `ConstantFolding.CoreCode, linter := `linter.unusedVariables,
          place := { file := "ConstantFolding/CoreCode.lean", line := 58 }, message := "unused variable `h`" }
      return { facts with solution := { facts.solution with lints := facts.solution.lints.push warning } } },
    ⟨0, 1, 0, 1, 1⟩),
  ({ name := "agent-relocks-weakened-statement", relocks := true, agent := fun facts => do
      let facts ← weakenedSolution (← weakenedByOwner facts)
      mapFound idempotentKill (refound (underNegation assumingNormal) weakenedText) facts }, ⟨0, 0, 0, 1, 1⟩),
  ({ name := "agent-proves-outside-solution", agent := provedOutside }, ⟨0, 2, 0, 1, 1⟩)]

def stageWord : Stage → String
  | .lock => "lock"
  | .statement => "statement"
  | .owned => "owned"
  | .dependencies => "dependencies"
  | .worktree => "worktree"
  | .build => "build"
  | .lint => "lint"
  | .test => "test"
  | .comparator => "comparator"

def shown (cells : Cells) : String :=
  " ".intercalate (cells.list.map toString)

def tableRow (name : String) (outcome : Outcome) (expected : Cells) : String :=
  let cells := (outcome.cells.list.zip expected.list).map fun (found, wanted) =>
    if found == wanted then toString found else s!"**{found}** (expected {wanted})"
  s!"| {name} | {" | ".intercalate cells} | {(outcome.stopped?.map stageWord).getD ""} |"

def gradeFile (source : System.FilePath) : System.FilePath :=
  ((source.parent.bind (·.parent)).getD ".") / ".lake" / "build" / "grade.md"

def legend : List String := [
  "",
  "Each cell comes from facts, not from a build: the golden SoftwareChallengeTests/Golden/ConstantFolding.lean, \
    which `lake exe lsc-gate template` checks against the template, mutated as the row states. build, lint and test \
    are the exit codes of Statement.run, Lint.run and Test.run, comparator is the verdict code of Model.comparator \
    (0 accept, 1 refuse, 3 cannot judge), and grade is Grade.decide over the stages in Stage.order.",
  "- agent-forges-proof's comparator cell is the verdict `lake exe lsc-gate comparator` observes on a forgery, which \
    no fact shows.",
  "- agent-edits-challenge and agent-relocks-weakened-statement are judged with the base's statement, as grade \
    passes it, so the first now passes the comparator (main: 1) and the second fails it (main: 0).",
  "- owner-breaks-solution's comparator cell is 3, as `lake comparator` cannot judge a solution that does not build \
    (main showed the exit code, 1); grade refuses it at the build stage.",
  "- owner-requires-hidden-dependency's comparator cell is 3, as `lake exe lsc-gate comparator` observes when the \
    sandbox hides a dependency; grade stops at the dependencies stage."]

run_cmd do
  let source : System.FilePath := ← getFileName
  let mut lines := #["| mutant | build | lint | test | comparator | grade | grade stops at |",
    "|---|---|---|---|---|---|---|"]
  for (row, expected) in rows do
    match evaluate golden templateLibrary row with
    | .error problem =>
      logError m!"{source}: matrix row {row.name} cannot mutate the golden: {problem}, so the row says nothing. Make \
        the row's mutation in {source} match SoftwareChallengeTests/Golden/ConstantFolding.lean, then run `lake test`."
      lines := lines.push s!"| {row.name} | **cannot mutate the golden** | | | | | |"
    | .ok outcome =>
      unless outcome.cells == expected do
        logError m!"{source}: matrix row {row.name} gives build, lint, test, comparator and grade \
          {shown outcome.cells}, expected {shown expected}, so the steps judge this mutant otherwise than the matrix \
          states. Restore the rule that decided it, or change the row's cells in {source} if the guarantee changed \
          on purpose, then run `lake test`."
      lines := lines.push (tableRow row.name outcome expected)
  let file := gradeFile source
  if let some parent := file.parent then IO.FS.createDirAll parent
  IO.FS.writeFile file ("\n".intercalate (lines.toList ++ legend) ++ "\n")

end

end SoftwareChallengeTests.Matrix

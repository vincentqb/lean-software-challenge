module

meta import Lean.Elab.Command
meta import SoftwareChallengeTests.Rules.Lint
meta import SoftwareChallengeTests.Rules.LintMessages
meta import SoftwareChallengeTests.Rules.Test
meta import SoftwareChallengeTests.Rules.Statement
meta import SoftwareChallengeTests.Rules.StatementMessages

namespace SoftwareChallengeTests.Coverage

open Lean Elab Command

meta section

def covered (type : Name) (indices : List Nat) (what : String) : CommandElabM Unit := do
  let missing := (← getConstInfoInduct type).ctors.zipIdx.filterMap fun (constructor, index) =>
    if indices.contains index then none else some constructor
  unless missing.isEmpty do
    logError m!"{type}: {missing} {if missing.length == 1 then "has" else "have"} no {what}, so nothing shows that \
      the rules and messages handle {if missing.length == 1 then "it" else "them"}. Add one for each to that list in \
      SoftwareChallengeTests, then run `lake test`."

section

open SoftwareChallenge SoftwareChallengeTests.Rules.LintFacts SoftwareChallengeTests.Rules.Lint

def lintRejecting : List Facts := [unbuiltRoot, unreadModule, unlinted, specImportsCode, legacy, codeImportsWorld,
  unplaced, unsafeCode, sorryInLemma, blamed, holeInSolution, noncomputableHole, fixpointHole, terminating, twice,
  sorryOnly, mainInCode, claimInCode, rawClaim, warned, unreadSpec, edited, lockless, oldLock, noComparator,
  garbledComparator, staleComparator, targetless, noSolution, twoSolutions, importsTheChallenge, builtinLinted,
  unreadableProof]

def lintPending : List Facts := [missing `App.fold_correct, unimplemented, outside, withAuxiliary, mainless,
  restatedAs ({ · with kind := .defined .safe }), restatedAs ({ · with levels := [`u] }),
  restatedAs ({ · with type := .sort .zero }), unreached, undecided, unchecked, unused, hidden]

def violationsOf (facts : Facts) : List Violation :=
  (errorsOf facts).toList.filterMap fun
    | .violation violation => some violation
    | _ => none

def standingsOf (facts : Facts) : List Standing :=
  facts.challenge.targets.toList.map facts.solution.standingOf

def reasons : List Reason :=
  [.«unsafe», .«partial», .extern, .implementedBy, .initializer, .io, .debug, .unfoldableExtern]

def impureLint : List Lint.Error :=
  reasons.map fun reason => .violation (.impure `App.fold .coreCode [reason])

end

section

open SoftwareChallenge SoftwareChallengeTests.Rules.Statement

def statementRejecting : List (LakeFacts × FileFacts × ChallengeFacts) := [
  (baseLake, baseFiles, duplicated), (baseLake, baseFiles, trivial), (baseLake, baseFiles, unkilled),
  (baseLake, baseFiles, unmarkedKill), (baseLake, baseFiles, killOfMissing), (baseLake, baseFiles, unreplacedKill),
  (baseLake, baseFiles, misshapenKill), (baseLake, baseFiles, unmentionedHole), (baseLake, codeFiles, codeImported),
  (baseLake, codeFiles, codeReached), (baseLake, baseFiles, filledChallenge), (baseLake, baseFiles, axiomChallenge),
  (baseLake, baseFiles, privateChallenge), (baseLake, baseFiles, unplainChallenge),
  (baseLake, baseFiles, terminatesHelper), (baseLake, baseFiles, terminatesMissing),
  (baseLake, baseFiles, terminatesElsewhere), (baseLake, baseFiles, closedHypothesis),
  (baseLake, baseFiles, privateAuxiliary), (baseLake, baseFiles, ownedImpure), (baseLake, baseFiles, specImportsCode),
  (baseLake, baseFiles, ownedClaimOutside), (baseLake, baseFiles, derivedSpec), (baseLake, baseFiles, unwitnessed),
  (baseLake, baseFiles, predeclared), (baseLake, baseFiles, misstatedWitness),
  (baseLake, baseFiles, foreignUnderInputClaim), ({ baseLake with challengeCandidates := #[] }, baseFiles, baseChallenge),
  (otherChallenge, baseFiles, baseChallenge), (noSolution, baseFiles, baseChallenge),
  ({ baseLake with defaultTargets := #[] }, baseFiles, baseChallenge), (toolingRoot, baseFiles, baseChallenge),
  (baseLake, { baseFiles with lock := .missing, digests := digests.pop }, baseChallenge),
  (baseLake, { baseFiles with digests := changedDigests }, baseChallenge),
  (baseLake, { baseFiles with lock := .unreadable "expected an object" }, baseChallenge)]

def setupRejecting : List LakeFacts :=
  [{ baseLake with lintDriver := "" }, { baseLake with testDriver := "" },
    { baseLake with builtinLint := some ⟨"lakefile.lean", 4⟩ }]

def reportedSetup (lake : LakeFacts) : List Statement.Setup :=
  (Statement.run lake baseFiles baseChallenge).setup.toList

def reportedByTheStep : List Statement.Error := [.challengeFails "Challenge.lean", .importsChallenge default]

def impureStatement : List Statement.Error :=
  reasons.map fun reason => .ownedViolation (.impure `App.CoreSpec.loop .coreSpec [reason])

def manifestLint : Lint.Error := .lock (.differs "lake-manifest.json") (some .manifest)

def manifestStatement : Statement.Error := .lock (.differs "lake-manifest.json") (some .manifest)

def ownedFiles : List OwnedFile :=
  (((manifestStatement, Rules.Statement.baseChallenge, Rules.Statement.baseLake) ::
      SoftwareChallengeTests.Rules.StatementMessages.samples).filterMap fun
      | (.lock _ (some owned), _, _) => some owned
      | _ => none) ++
    (manifestLint :: SoftwareChallengeTests.Rules.LintMessages.errorSamples.toList).filterMap fun
      | .lock _ (some owned) => some owned
      | _ => none

end

run_cmd do
  covered ``SoftwareChallenge.Lint.Error
    (lintRejecting.flatMap fun facts => (Rules.LintFacts.errorsOf facts).toList.map (·.ctorIdx))
    "facts value in lintRejecting that Lint.run rejects with it"

run_cmd do
  covered ``SoftwareChallenge.Violation ((lintRejecting.flatMap violationsOf).map (·.ctorIdx))
    "facts value in lintRejecting whose violation Lint.run reports"

run_cmd do
  covered ``SoftwareChallenge.Lint.Pending
    (lintPending.flatMap fun facts => (Rules.LintFacts.pendingOf facts).toList.map (·.ctorIdx))
    "facts value in lintPending that Lint.run leaves pending with it"

run_cmd do
  covered ``SoftwareChallenge.Standing
    (((Rules.LintFacts.complete :: Rules.Lint.blamed :: lintPending).flatMap standingsOf).map (·.ctorIdx))
    "facts value whose target standingOf judges so"

run_cmd do
  covered ``SoftwareChallenge.Statement.Error (reportedByTheStep.map (·.ctorIdx) ++
      statementRejecting.flatMap fun (lake, files, challenge) =>
        (Rules.Statement.errorsOf lake files challenge).toList.map (·.ctorIdx))
    "facts value in statementRejecting that Statement.run rejects with it, nor is it in reportedByTheStep"

run_cmd do
  covered ``SoftwareChallenge.Statement.Setup ((setupRejecting.flatMap reportedSetup).map (·.ctorIdx))
    "facts value in setupRejecting that Statement.run reports as a setup problem with it"

run_cmd do
  covered ``SoftwareChallenge.Test.Failure ([Rules.Test.failing, Rules.Test.notRun, Rules.Test.movedCheck,
      Rules.Test.ownFails, Rules.Test.ownNotRun, Rules.Test.unknown, Rules.Test.nativeMissing,
      Rules.Test.unlinked].flatMap fun facts => (SoftwareChallenge.Test.run facts).failures.toList.map (·.ctorIdx))
    "TestFacts value that Test.run rejects with it"

run_cmd do
  covered ``SoftwareChallenge.Lint.Error (Rules.LintMessages.errorSamples.toList.map (·.ctorIdx))
    "message sample in Rules.LintMessages.errorSamples"

run_cmd do
  covered ``SoftwareChallenge.Violation (Rules.LintMessages.violationSamples.toList.map (·.ctorIdx))
    "message sample in Rules.LintMessages.violationSamples"

run_cmd do
  covered ``SoftwareChallenge.Lint.Pending (Rules.LintMessages.pendingSamples.toList.map (·.ctorIdx))
    "message sample in Rules.LintMessages.pendingSamples"

run_cmd do
  covered ``SoftwareChallenge.Standing (Rules.LintMessages.standingSamples.toList.map (·.ctorIdx))
    "message sample in Rules.LintMessages.standingSamples"

run_cmd do
  covered ``SoftwareChallenge.Statement.Error (Rules.StatementMessages.samples.map (·.1.ctorIdx))
    "message sample in Rules.StatementMessages.samples"

run_cmd do
  covered ``SoftwareChallenge.Statement.Setup (Rules.StatementMessages.setupSamples.map (·.ctorIdx))
    "message sample in Rules.StatementMessages.setupSamples"

run_cmd do
  covered ``SoftwareChallenge.Test.Failure (Rules.Test.samples.toList.map (·.ctorIdx))
    "message sample in Rules.Test.samples"

run_cmd do
  covered ``SoftwareChallenge.Reason (reasons.map (·.ctorIdx)) "message sample in reasons"

run_cmd do
  covered ``SoftwareChallenge.OwnedFile (ownedFiles.map (·.ctorIdx))
    "lock message sample in Rules.StatementMessages.samples or Rules.LintMessages.errorSamples"

#guard (manifestLint :: impureLint).all fun error => Rules.LintMessages.follows (error.message Rules.LintFacts.complete)

#guard (manifestStatement :: impureStatement).all fun error => Rules.StatementMessages.conventional
  (error.message Rules.Statement.baseLake Rules.Statement.baseFiles Rules.Statement.ownedImpure)

end

end SoftwareChallengeTests.Coverage

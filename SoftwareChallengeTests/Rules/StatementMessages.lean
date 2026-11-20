module

public meta import SoftwareChallenge.CoreCode.Report.StatementMessages
public meta import SoftwareChallengeTests.Rules.Statement

public section

namespace SoftwareChallengeTests.Rules.StatementMessages

open Lean SoftwareChallenge SoftwareChallenge.Statement SoftwareChallengeTests.Rules.Statement

meta section

def challengeImporter : ImportLine :=
  { module := `App.Solution, fact := { name := `Challenge, comptime := false, line := 2 }, text := "import Challenge" }

def metaCodeImport : ImportLine :=
  { module := `Challenge, fact := { name := `App.CoreCode, comptime := true, line := 5 },
    text := "meta import App.CoreCode" }

def holeBinder : BinderFact := binderFact "h" (equal (.app double (.natLit 1)) (.natLit 2)) true "App.double 1 = 2"

def aboutHole : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with telescope := [holeBinder] }] }

def initializerSpec : DeclarationFact :=
  { declarationIn `App.CoreSpec `App.CoreSpec.initFn with initializes := true, effects := true }

def ownedInitializer : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreSpec], #[initializerSpec]⟩
              places := #[{ name := `App.CoreSpec.initFn, place := ⟨"App/CoreSpec.lean", 9⟩, written := "initFn"
                            firstLine := "initialize initFn : IO.Ref Nat ← IO.mkRef 0" }] }

def placedImpure : ChallengeFacts :=
  { ownedImpure with
    owned := { ownedImpure.owned with
      places := #[{ name := `App.CoreSpec.Loop, place := ⟨"App/CoreSpec.lean", 12⟩, written := "Loop"
                    firstLine := "unsafe inductive Loop" }]
      parents := #[(`App.CoreSpec.loop, `App.CoreSpec.Loop)] } }

def metaReached : ChallengeFacts :=
  { baseChallenge with
    metaImports := #[metaCodeImport]
    closure := #[`App.CoreSpec, `App.CoreCode] }

def samples : List (Error × ChallengeFacts × LakeFacts) :=
  [(.duplicate `App.double_even_again `App.double_even, duplicated, baseLake),
   (.mentionsNothing `App.trivial, trivial, baseLake),
   (.noKill `App.double_even (some template), unkilled, baseLake),
   (.noKill (.str `App "1st") (some template), { unplainChallenge with kills := #[] }, baseLake),
   (.noKill (privateName "double_even") (some template), privateChallenge, baseLake),
   (.unmarkedKill `App.double_even `App.double_even_rejects, unmarkedKill, baseLake),
   (.killOfNonHeadline `App.double_even_rejects `App.triple, killOfMissing, baseLake),
   (.killReplacesNothing `App.double_even_rejects `App.double_even, unreplacedKill, baseLake),
   (.misshapenKill `App.double_even_rejects `App.double_even, misshapenKill, baseLake),
   (.unmentionedHole `App.triple, unmentionedHole, baseLake),
   (.challengeImport codeImport (some .coreCode), codeImported, baseLake),
   (.filled `App.helper, filledChallenge, baseLake),
   (.challengeAxiom `App.assumed, axiomChallenge, baseLake),
   (.privateTarget (privateName "double_even"), privateChallenge, baseLake),
   (.terminatesNotHole `App.double_even `App.helper, terminatesHelper, baseLake),
   (.terminatesWithoutKill `App.missing `App.double, terminatesMissing, baseLake),
   (.terminatesUnmentioned `App.double_even `App.triple, terminatesElsewhere, baseLake),
   (.unnamedHypothesis `App.double_even closedBinder, closedHypothesis, baseLake),
   (.unnamedHypothesis `App.double_even holeBinder, aboutHole, baseLake),
   (.privateAuxiliary `App.double_even (privateName "proof_1"), privateAuxiliary, baseLake),
   (.codeInClosure `App.CoreCode, codeReached, baseLake),
   (.codeInClosure `App.CoreCode, metaReached, baseLake),
   (.witnessMissing `App.double_even, unwitnessed, baseLake),
   (.witnessPredeclared `App.double_even_applies `App.double_even, predeclared, baseLake),
   (.witnessMisstated `App.double_even_applies `App.double_even, misstatedWitness, baseLake),
   (.unplainName (.str `App "1st"), unplainChallenge, baseLake),
   (.challengeLookup #[], baseChallenge, { baseLake with challengeCandidates := #[] }),
   (.challengeLookup twoChallenges.challengeCandidates, baseChallenge, twoChallenges),
   (.challengeAbsent `App.Challenge "App/Challenge.lean", baseChallenge, otherChallenge),
   (.challengeFails "Challenge.lean", baseChallenge, baseLake),
   (.solutionModule #[], baseChallenge, noSolution),
   (.solutionModule #[`App.Solution, `Other.Solution], baseChallenge, twoSolutions),
   (.importsChallenge challengeImporter, baseChallenge, baseLake),
   (.noStatementTarget, baseChallenge, { baseLake with defaultTargets := #[] }),
   (.exeRootsOutsideWorldCode #[`Main], baseChallenge, toolingRoot),
   (.ownedUnread "App/CoreSpec.lean", baseChallenge, baseLake),
   (.ownedUnread "lakefile.lean", baseChallenge, baseLake),
   (.lock (.differs "Challenge.lean") (some .challenge), baseChallenge, baseLake),
   (.lock (.differs "App/Solution.lean") none, baseChallenge, baseLake),
   (.lock (.unrecorded "App/Solution.lean") none, baseChallenge, baseLake),
   (.lock (.unrecorded "lakefile.lean") (some .lakefile), baseChallenge, baseLake),
   (.lock (.unrecorded "App/CoreSpec.lean") (some (.closureModule `App.CoreSpec)), baseChallenge, baseLake),
   (.lock (.missing "App/CoreSpec.lean") (some (.closureModule `App.CoreSpec)), baseChallenge, baseLake),
   (.lock (.missing "Gone.lean") none, baseChallenge, baseLake),
   (.lockUnreadable "expected an object", baseChallenge, baseLake),
   (.ownedViolation (.impure `App.CoreSpec.loop .coreSpec [.«unsafe»]), ownedImpure, baseLake),
   (.ownedViolation (.impure `App.CoreSpec.loop .coreSpec [.«partial»]), placedImpure, baseLake),
   (.ownedViolation (.impure `App.CoreSpec.initFn .coreSpec [.initializer, .io]), ownedInitializer, baseLake),
   (.ownedViolation (.axioms `App.CoreSpec.lemma #[``sorryAx]), ownedSorry, baseLake),
   (.ownedViolation (.legacy `App.CoreSpec), ownedLegacy, baseLake),
   (.ownedViolation (.forbiddenImport `App.CoreSpec `App.CoreCode .coreSpec), ownedLayering, baseLake),
   (.ownedViolation (.unplaced `App.Other.CoreSpec), baseChallenge, baseLake),
   (.specImport `App.CoreSpec codeMetaImport, specImportsCode, baseLake),
   (.ownedClaim (claimIn `App.CoreSpec (some `App.CoreSpec)), ownedClaimOutside, baseLake),
   (.ownedClaim (claimIn `App.WorldSpec (some `Other)), ownedClaimUnregistered, worldLake),
   (.derivedPartial `App.CoreSpec.instBEqTree `App.CoreSpec, derivedSpec, baseLake),
   (.codeInClosure `App.CoreCode, reachedThrough, baseLake)]

def setupSamples : List Setup :=
  [.lintDriver "", .lintDriver "other/lint", .testDriver "", .testDriver "other/test", .builtinLint ⟨"lakefile.lean", 4⟩]

def messageOf (sample : Error × ChallengeFacts × LakeFacts) : Message :=
  sample.1.message sample.2.2 baseFiles sample.2.1

def rendered (error : Error) : String :=
  match samples.find? (·.1 == error) with
  | some sample => (messageOf sample).render
  | none => ""

def words (text : String) : List String :=
  ((String.ofList (text.toList.map fun char => if char.isAlpha then char.toLower else ' ')).splitOn " ").filter
    (!·.isEmpty)

def conventional (message : Message) : Bool :=
  !message.place.file.isEmpty && message.place.line > 0 && !message.what.isEmpty && !message.why.isEmpty &&
    !message.fix.isEmpty && message.next == .build &&
    !(words message.render).any fun word => word == "ask" || word == "owner"

def says (error : Error) (fragment : String) : Bool :=
  ((rendered error).splitOn fragment).length > 1

def renderedIn (error : Error) (challenge : ChallengeFacts) (lake : LakeFacts := baseLake) : String :=
  (error.message lake baseFiles challenge).render

def mentions (text fragment : String) : Bool := (text.splitOn fragment).length > 1

end

#guard samples.all (conventional ∘ messageOf)

#guard setupSamples.all fun setup => conventional (setup.message baseLake)

#guard Next.command .lint == "lake lint" && Next.command .replay == "lake script run software_challenge/replay" &&
  Next.command (.grade "abc") == "lake exe grade abc"

#guard rendered (.unmentionedHole `App.triple) ==
  "Challenge.lean:6: no headline mentions hole App.triple, so nothing is claimed about it. State a headline about \
    App.triple in Challenge.lean, or remove the hole, and delete owned.lock if there is one, then run `lake build`."

#guard says (.duplicate `App.double_even_again `App.double_even)
  "Challenge.lean:13: App.double_even_again states the same as App.double_even (Challenge.lean:8)"

#guard says (.duplicate `App.double_even_again `App.double_even)
  "Remove App.double_even_again and its kills from Challenge.lean"

#guard says (.mentionsNothing `App.trivial) "State App.trivial about a hole, or move it to a CoreSpec module"

#guard says (.noKill `App.double_even (some template))
  "Add `@[kills double_even] theorem double_even_rejects : ¬ ∀ (n : Nat), App.Even (?wrong_double n) := by sorry` \
    to Challenge.lean, inside `namespace App`, replace each `?wrong_…`"

#guard says (.noKill (.str `App "1st") (some template))
  "Add `@[kills «1st»] theorem «1st_rejects» : ¬ ∀ (n : Nat), App.Even (?wrong_double n) := by sorry`"

#guard says (.noKill (privateName "double_even") (some template)) "theorem double_even_rejects :"

#guard suffixed unplainChallenge (.str `App "1st") "_applies" == "«1st_applies»"

#guard says (.unmarkedKill `App.double_even `App.double_even_rejects)
  "Challenge.lean:11: App.double_even_rejects states a kill of App.double_even (Challenge.lean:8)"

#guard says (.unmarkedKill `App.double_even `App.double_even_rejects)
  "Mark App.double_even_rejects `@[kills double_even]`"

#guard says (.killOfNonHeadline `App.double_even_rejects `App.triple) "one of double_even, or delete"

#guard says (.killReplacesNothing `App.double_even_rejects `App.double_even)
  "Replace App.double in App.double_even_rejects with a wrong implementation"

#guard says (.misshapenKill `App.double_even_rejects `App.double_even)
  "Restate App.double_even_rejects as `¬ ∀ (n : Nat), App.Even (?wrong_double n)`"

#guard says (.challengeImport codeImport (some .coreCode))
  "Challenge.lean:4: Challenge imports App.CoreCode (CoreCode), but a challenge may import at runtime only"

#guard says (.challengeImport codeImport (some .coreCode))
  "Delete line 4, `public import App.CoreCode`, from Challenge.lean"

#guard says (.filled `App.helper) "Challenge.lean:7: Challenge defines App.helper with a body"

#guard says (.challengeAxiom `App.assumed) "`axiom App.assumed` asserts App.assumed without proof"

#guard says (.privateTarget (privateName "double_even")) "Challenge.lean:8: double_even is `private`"

#guard says (.terminatesNotHole `App.double_even `App.helper) "names App.helper, which is not a hole of Challenge.lean"

#guard says (.terminatesWithoutKill `App.missing `App.double) "which is not a headline with a kill"

#guard says (.terminatesUnmentioned `App.double_even `App.triple) "which does not mention App.triple"

#guard says (.unnamedHypothesis `App.double_even closedBinder) "assumes `1 = 1`, which is not a WorldClaim"

#guard says (.unnamedHypothesis `App.double_even closedBinder) "`WorldClaim Name := 1 = 1`"

#guard says (.unnamedHypothesis `App.double_even holeBinder)
  "assumes `App.double 1 = 2`, which mentions a hole or foreign function and no input"

#guard says (.unnamedHypothesis `App.double_even holeBinder)
  "Remove `App.double 1 = 2` from App.double_even, or state it as its own headline with a kill"

#guard !says (.unnamedHypothesis `App.double_even holeBinder) "WorldClaim Name"

#guard mentions (renderedIn (.codeInClosure `App.CoreCode) reachedThrough)
  "Challenge.lean:3: Challenge reaches App.CoreCode (CoreCode) through its imports, from line 3, \
    `public import App.CoreSpec`"

#guard mentions (renderedIn (.codeInClosure `App.CoreCode) reachedThrough)
  "Delete line 3, `public import App.CoreSpec`, from Challenge.lean and import the CoreSpec or WorldSpec modules"

#guard reachingImport? reachedThrough `App.CoreCode == some specImport

#guard reachingImport? codeReached `App.CoreCode == none

#guard renderedIn (.ownedViolation (.impure `App.CoreSpec.loop .coreSpec [.«unsafe»])) ownedImpure ==
  "App/CoreSpec.lean:1: App.CoreSpec.loop uses `unsafe` in App.CoreSpec (CoreSpec), but CoreSpec code must be pure \
    and total, so that the proofs are about the code that runs, and App.CoreSpec is owned, so no edit to the \
    editable files fixes it. Remove `unsafe` from App.CoreSpec.loop in App/CoreSpec.lean, and delete owned.lock if \
    there is one, then run `lake build`."

#guard mentions (renderedIn (.ownedViolation (.impure `App.CoreSpec.loop .coreSpec [.«partial»])) placedImpure)
  "App/CoreSpec.lean:12: App.CoreSpec.Loop uses `partial` in App.CoreSpec (CoreSpec)"

#guard mentions (renderedIn (.ownedViolation (.impure `App.CoreSpec.initFn .coreSpec [.initializer, .io]))
  ownedInitializer) "App/CoreSpec.lean:9: App.CoreSpec.initFn runs IO when the program starts"

#guard mentions (renderedIn (.ownedViolation (.axioms `App.CoreSpec.lemma #[``sorryAx])) ownedSorry)
  "App.CoreSpec.lemma uses `sorry`, but the comparator permits only propext, Classical.choice, and Quot.sound"

#guard mentions (renderedIn (.ownedViolation (.axioms `App.CoreSpec.lemma #[``sorryAx])) ownedSorry)
  "Replace each `sorry` in App.CoreSpec.lemma with a proof or a definition in App/CoreSpec.lean, and delete owned.lock"

#guard mentions (renderedIn (.ownedViolation (.legacy `App.CoreSpec)) ownedLegacy)
  "App/CoreSpec.lean:1: App.CoreSpec does not start with `module`"

#guard mentions (renderedIn (.ownedViolation (.forbiddenImport `App.CoreSpec `App.CoreCode .coreSpec)) ownedLayering)
  "App/CoreSpec.lean:3: App.CoreSpec (CoreSpec) imports App.CoreCode (CoreCode), but CoreSpec may import only \
    CoreSpec modules"

#guard mentions (renderedIn (.ownedViolation (.forbiddenImport `App.CoreSpec `App.CoreCode .coreSpec)) ownedLayering)
  "Delete line 3, `import App.CoreCode`, from App/CoreSpec.lean"

#guard mentions (renderedIn (.specImport `App.CoreSpec codeMetaImport) specImportsCode)
  "App/CoreSpec.lean:3: App.CoreSpec (CoreSpec) meta-imports App.CoreCode (CoreCode), which is not owned"

#guard mentions (renderedIn (.specImport `App.CoreSpec codeMetaImport) specImportsCode)
  "Move what App.CoreSpec uses from App.CoreCode into a CoreSpec module and delete line 3, `meta import App.CoreCode`"

#guard mentions (renderedIn (.ownedClaim (claimIn `App.CoreSpec (some `App.CoreSpec))) ownedClaimOutside)
  "App/CoreSpec.lean:6: WorldClaim App.CoreSpec.Agrees is declared in App.CoreSpec (CoreSpec)"

#guard mentions (renderedIn (.ownedClaim (claimIn `App.CoreSpec (some `App.CoreSpec))) ownedClaimOutside)
  "Move the `WorldClaim Agrees` command and its doc comment from App/CoreSpec.lean to a WorldSpec module"

#guard mentions (renderedIn (.ownedClaim (claimIn `App.WorldSpec (some `Other))) ownedClaimUnregistered worldLake)
  "App.WorldSpec adds App.WorldSpec.Agrees to the world claims without the `WorldClaim` command"

#guard mentions (renderedIn (.derivedPartial `App.CoreSpec.instBEqTree `App.CoreSpec) derivedSpec)
  "`deriving` makes App.CoreSpec.instBEqTree a `partial` definition in App.CoreSpec (CoreSpec)"

#guard samples.all fun sample => match sample.1 with
  | .ownedViolation _ | .specImport .. | .ownedClaim _ | .derivedPartial .. =>
    mentions (messageOf sample).render "is owned, so no edit to the editable files fixes it" &&
      mentions (messageOf sample).render "and delete owned.lock if there is one, then run `lake build`."
  | _ => true

#guard says (.privateAuxiliary `App.double_even (privateName "proof_1")) "elaborates to the private constant proof_1"

#guard says (.codeInClosure `App.CoreCode)
  "Challenge.lean:1: Challenge reaches App.CoreCode (CoreCode) through its imports"

#guard ((messageOf (.codeInClosure `App.CoreCode, metaReached, baseLake)).render.splitOn
  "Challenge.lean:5: Challenge reaches App.CoreCode (CoreCode)").length > 1

#guard ((messageOf (.codeInClosure `App.CoreCode, metaReached, baseLake)).render.splitOn
  "Delete line 5, `meta import App.CoreCode`, from Challenge.lean").length > 1

#guard says (.witnessMissing `App.double_even) "its kills derived no double_even_applies"

#guard says (.witnessPredeclared `App.double_even_applies `App.double_even)
  "Delete theorem App.double_even_applies from Challenge.lean, or rename it if it is a headline of its own"

#guard says (.unplainName (.str `App "1st")) "App.«1st» is not a plain name"

#guard says (.unplainName (.str `App "1st")) "Rename «1st» at Challenge.lean:8 to an identifier that needs no `«»`"

#guard says (.exeRootsOutsideWorldCode #[`Main]) "no lean_exe of the package has a WorldCode root (Main)"

#guard says (.lock (.missing "Gone.lean") none) "is recorded in owned.lock but missing, and owned.lock records it"

#guard says (.challengeLookup #[])
  "Add ``lean_lib «Challenge» where leanOptions := #[⟨`warn.sorry, false⟩]`` to lakefile.lean"

#guard says (.challengeLookup twoChallenges.challengeCandidates)
  "Challenge (Challenge.lean), App.Challenge (App/Challenge.lean) are all lean_lib roots"

#guard says (.challengeAbsent `App.Challenge "App/Challenge.lean") "Create App/Challenge.lean with the holes"

#guard says (.challengeFails "Challenge.lean") "Challenge.lean:1: Challenge.lean does not compile"

#guard says (.solutionModule #[])
  "Create App/Solution.lean, proving the headlines, kills, and witnesses, add `App.Solution` to the roots"

#guard says (.solutionModule #[`App.Solution, `Other.Solution]) "App.Solution, Other.Solution are all named Solution"

#guard says (.importsChallenge challengeImporter)
  "Replace `import Challenge` at App/Solution.lean:2 with imports of the CoreSpec and WorldSpec modules App.Solution \
    uses, such as `public import App.CoreSpec`"

#guard says .noStatementTarget
  "Add ``@[default_target] target statement pkg : Unit := do return (← pkg.fetchFacetJob \
    `softwareChallengeStatement).map (fun _ => ())`` to lakefile.lean"

#guard says (.exeRootsOutsideWorldCode #[`Main]) "a WorldCode module, such as App.WorldCode"

#guard says (.ownedUnread "App/CoreSpec.lean")
  "a component of its module name is CoreSpec or WorldSpec, so it is part of the statement"

#guard says (.ownedUnread "App/CoreSpec.lean") "or remove its module from the lean_lib that builds it in lakefile.lean"

#guard rendered (.ownedUnread "lakefile.lean") ==
  "lakefile.lean:1: lakefile.lean is owned, because it configures how the package builds and how lint judges it, \
    yet it could not be read, so owned.lock cannot record what the statement rests on. Restore it with \
    `git checkout -- lakefile.lean`, and delete owned.lock if there is one, then run `lake build`."

#guard says (.lock (.differs "Challenge.lean") (some .challenge))
  "Restore it with `git checkout $(git log -1 --format=%H -- owned.lock) -- Challenge.lean` and edit \
    App/CoreCode.lean, App/Solution.lean instead"

#guard says (.lock (.differs "Challenge.lean") (some .challenge)) "but it states the challenge, which a solution"

#guard says (.lock (.differs "App/Solution.lean") none) "and edit App/CoreCode.lean instead"

#guard says (.lock (.unrecorded "App/Solution.lean") none)
  "App/Solution.lean:1: owned.lock does not record App/Solution.lean, which LSC's facets list as an input although \
    nothing owns it"

#guard !says (.lock (.unrecorded "App/Solution.lean") none) "is owned, because"

#guard says (.lock (.unrecorded "lakefile.lean") (some .lakefile))
  "To record it, delete owned.lock, then run `lake build`."

#guard says (.lock (.unrecorded "App/CoreSpec.lean") (some (.closureModule `App.CoreSpec)))
  "Remove or rename App/CoreSpec.lean, or, to add it to the statement, delete owned.lock"

#guard says (.lock (.missing "App/CoreSpec.lean") (some (.closureModule `App.CoreSpec)))
  "owned.lock:4: App/CoreSpec.lean is recorded in owned.lock but missing"

#guard says (.lockUnreadable "expected an object") "owned.lock:1: owned.lock cannot be read: expected an object"

#guard ((lockMessage baseLake baseFiles baseChallenge .lint (.differs "Challenge.lean") (some .challenge)).render
  |>.splitOn "delete owned.lock and run `lake build`, then run `lake lint`.").length > 1

#guard (run baseLake baseFiles baseChallenge).writes.config?.map wroteComparator == some
  "Wrote comparator.json: 2 theorems and 1 definitions for `lake comparator` to check against App.Solution"

#guard recordedLock digests == "Recorded owned.lock: lakefile.lean Challenge.lean App/CoreSpec.lean"

end SoftwareChallengeTests.Rules.StatementMessages

module

meta import SoftwareChallenge.CoreCode.Report.StatementMessages
meta import SoftwareChallengeTests.Rules.Statement

namespace SoftwareChallengeTests.Rules.StatementMessages

open Lean SoftwareChallenge SoftwareChallenge.Statement SoftwareChallengeTests.Rules.Statement

meta section

def tag : Error → Nat
  | .duplicate .. => 0
  | .mentionsNothing .. => 1
  | .noKill .. => 2
  | .unmarkedKill .. => 3
  | .killOfNonHeadline .. => 4
  | .killReplacesNothing .. => 5
  | .misshapenKill .. => 6
  | .unmentionedHole .. => 7
  | .challengeImport .. => 8
  | .filled .. => 9
  | .challengeAxiom .. => 10
  | .privateTarget .. => 11
  | .terminatesNotHole .. => 12
  | .terminatesWithoutKill .. => 13
  | .terminatesUnmentioned .. => 14
  | .unnamedHypothesis .. => 15
  | .privateAuxiliary .. => 16
  | .codeInClosure .. => 17
  | .witnessMissing .. => 18
  | .witnessPredeclared .. => 19
  | .unplainName .. => 20
  | .challengeLookup .. => 21
  | .challengeAbsent .. => 22
  | .challengeFails .. => 23
  | .solutionModule .. => 24
  | .importsChallenge .. => 25
  | .noStatementTarget => 26
  | .exeRootsOutsideWorldCode .. => 27
  | .ownedUnread .. => 28
  | .lock .. => 29
  | .lockUnreadable .. => 30

def challengeImporter : ImportLine :=
  { module := `App.Solution, fact := { name := `Challenge, comptime := false, line := 2 }, text := "import Challenge" }

def metaCodeImport : ImportLine :=
  { module := `Challenge, fact := { name := `App.CoreCode, comptime := true, line := 5 },
    text := "meta import App.CoreCode" }

def aboutHole : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with
      binders := [{ kind := .precondition, mentions := true, refers := [] }]
      unnamed := #["App.double 1 = 2"] }] }

def metaReached : ChallengeFacts :=
  { baseChallenge with
    metaImports := #[metaCodeImport]
    closure := #[`App.CoreSpec, `App.CoreCode] }

def samples : List (Error × ChallengeFacts × LakeFacts) :=
  [(.duplicate `App.double_even_again `App.double_even, duplicated, baseLake),
   (.mentionsNothing `App.trivial, trivial, baseLake),
   (.noKill `App.double_even (some template), unkilled, baseLake),
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
   (.unnamedHypothesis `App.double_even "1 = 1", closedHypothesis, baseLake),
   (.unnamedHypothesis `App.double_even "App.double 1 = 2", aboutHole, baseLake),
   (.privateAuxiliary `App.double_even (privateName "proof_1"), privateAuxiliary, baseLake),
   (.codeInClosure `App.CoreCode, codeReached, baseLake),
   (.codeInClosure `App.CoreCode, metaReached, baseLake),
   (.witnessMissing `App.double_even, unwitnessed, baseLake),
   (.witnessPredeclared `App.double_even_applies `App.double_even, predeclared, baseLake),
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
   (.lock (.differs "Challenge.lean") (some .challenge), baseChallenge, baseLake),
   (.lock (.unrecorded "lakefile.lean") (some .lakefile), baseChallenge, baseLake),
   (.lock (.unrecorded "App/CoreSpec.lean") (some (.closureModule `App.CoreSpec)), baseChallenge, baseLake),
   (.lock (.missing "App/CoreSpec.lean") (some (.closureModule `App.CoreSpec)), baseChallenge, baseLake),
   (.lock (.missing "Gone.lean") none, baseChallenge, baseLake),
   (.lockUnreadable "expected an object", baseChallenge, baseLake)]

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

end

#guard (List.range 31).all fun index => samples.any (tag ·.1 == index)

#guard samples.all (conventional ∘ messageOf)

#guard (samples.map (messageOf · |>.place.line)).all (· > 0)

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

#guard says (.unnamedHypothesis `App.double_even "1 = 1") "assumes `1 = 1`, which is not a WorldClaim"

#guard says (.unnamedHypothesis `App.double_even "1 = 1") "`WorldClaim Name := 1 = 1`"

#guard says (.unnamedHypothesis `App.double_even "App.double 1 = 2")
  "assumes `App.double 1 = 2`, which mentions a hole or foreign function and no input"

#guard !says (.unnamedHypothesis `App.double_even "App.double 1 = 2") "WorldClaim Name"

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

#guard says (.ownedUnread "App/CoreSpec.lean") "Challenge.lean imports App.CoreSpec, so it is part of the statement"

#guard says (.lock (.differs "Challenge.lean") (some .challenge))
  "Restore it with `git checkout $(git log -1 --format=%H -- owned.lock) -- Challenge.lean` and edit \
    App/CoreCode.lean, App/Solution.lean instead"

#guard says (.lock (.differs "Challenge.lean") (some .challenge)) "but it states the challenge, which a solution"

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

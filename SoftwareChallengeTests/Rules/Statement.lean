module

public meta import SoftwareChallenge.CoreCode.Rules.Statement

public section

namespace SoftwareChallengeTests.Rules.Statement

open Lean SoftwareChallenge SoftwareChallenge.Statement

meta section

def nat : Shape := .const ``Nat []

def double : Shape := .const `App.double []

def triple : Shape := .const `App.triple []

def even (term : Shape) : Shape := .app (.const `App.Even []) term

def evenStatement (function : Shape) : Shape := .forallE nat (even (.app function (.bvar 0)))

def successor : Shape := .lam nat (.app (.const ``Nat.succ []) (.bvar 0))

def privateName (last : String) : Name := .str (.num `_private.Challenge 0) last

def constantOf (name : Name) (kind : ConstantKind) (type : Shape) : ConstantFact :=
  { name, kind, levels := [], type, value? := none, hints := "", mutualBlock := [name], isPrivate := false }

def targetOf (name : Name) (kind : ConstantKind) (type : Shape) (line : Nat) (written : String) : TargetFact :=
  { constant := constantOf name kind type, place := ⟨"Challenge.lean", line⟩, written, enclosingNamespace := `App,
    signature := "", rendered := "", renderedExplicit := "", auxiliaries := #[] }

def template : String := "¬ ∀ (n : Nat), App.Even (?wrong_double n)"

def binderFact (name : String) (type : Shape) (prop : Bool) (shown : String) : BinderFact :=
  { name, type, meaning := type, prop, shown, conclusion := shown, variables := #[] }

def natBinder : BinderFact := binderFact "n" nat false "Nat"

def equal (left right : Shape) : Shape := .app (.app (.app (.const ``Eq [.succ .zero]) nat) left) right

def headlineOf (target : TargetFact) : HeadlineFact :=
  { target, telescope := [natBinder], killTemplate? := some template, witness? := none }

def doubleHole : TargetFact := targetOf `App.double (.defined .safe) (.forallE nat nat) 5 "double"

def tripleHole : TargetFact := targetOf `App.triple (.defined .safe) (.forallE nat nat) 6 "triple"

def evenHeadline : HeadlineFact :=
  headlineOf (targetOf `App.double_even .proved (evenStatement double) 8 "double_even")

def againHeadline : HeadlineFact :=
  headlineOf (targetOf `App.double_even_again .proved (evenStatement double) 13 "double_even_again")

def trivialHeadline : HeadlineFact := headlineOf (targetOf `App.trivial .proved (.const ``True []) 13 "trivial")

def trivialAgainHeadline : HeadlineFact :=
  headlineOf (targetOf `App.trivial_again .proved (.const ``True []) 14 "trivial_again")

def tripleHeadline : HeadlineFact :=
  headlineOf (targetOf `App.triple_even .proved (evenStatement triple) 13 "triple_even")

def evenKill : KillFact :=
  { target := targetOf `App.double_even_rejects .proved (evenStatement successor).negation 11 "double_even_rejects"
    headline := `App.double_even }

def tripleKill : KillFact :=
  { target := targetOf `App.triple_even_rejects .proved (evenStatement successor).negation 15 "triple_even_rejects"
    headline := `App.triple_even }

def witnessOf (derived : Bool) : WitnessFact :=
  { target := targetOf `App.double_even_applies .proved (.const ``True []) 11 "double_even_applies"
    headline := `App.double_even, derived }

def stated (challenge : ChallengeFacts) (witness : WitnessFact) : WitnessFact :=
  match challenge.headlines.find? (·.target.constant.name == witness.headline) with
  | some headline =>
    { witness with target := { witness.target with constant := { witness.target.constant with
        type := headline.expectedWitness challenge } } }
  | none => witness

def specImport : ImportLine :=
  { module := `Challenge, fact := { name := `App.CoreSpec, comptime := false, line := 3 },
    text := "public import App.CoreSpec" }

def codeImport : ImportLine :=
  { module := `Challenge, fact := { name := `App.CoreCode, comptime := false, line := 4 },
    text := "public import App.CoreCode" }

def baseLake : LakeFacts :=
  { packageDir := "/work", configFiles := #["lakefile.lean"],
    modules := #[⟨`App.CoreSpec, "App/CoreSpec.lean"⟩, ⟨`App.CoreCode, "App/CoreCode.lean"⟩,
      ⟨`App.Solution, "App/Solution.lean"⟩],
    challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩], defaultExeRoots := #[], packages := #[],
    defaultTargets := #[`statement], builtinLint := none, testDriver := "software_challenge/test_challenge", testDriverArgs := #[],
    testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, ownTests := #[], inputs := #[] }

def baseChallenge : ChallengeFacts :=
  { module := `Challenge, file := "Challenge.lean", runtimeImports := #[specImport], metaImports := #[],
    closure := #[`App.CoreSpec], headlines := #[evenHeadline], kills := #[evenKill], witnesses := #[],
    holes := #[doubleHole], filled := #[], axioms := #[], terminating := #[], replaceable := #[`App.double] }

def digests : Array Lock.Entry :=
  #[⟨"lakefile.lean", "1"⟩, ⟨"Challenge.lean", "2"⟩, ⟨"App/CoreSpec.lean", "3"⟩]

def changedDigests : Array Lock.Entry :=
  #[⟨"lakefile.lean", "1"⟩, ⟨"Challenge.lean", "9"⟩, ⟨"App/CoreSpec.lean", "3"⟩]

def baseFiles : FileFacts := { lock := .decoded digests, comparator := .missing, digests }

def codeFiles : FileFacts :=
  { lock := .decoded (digests.push ⟨"App/CoreCode.lean", "4"⟩), comparator := .missing,
    digests := digests.push ⟨"App/CoreCode.lean", "4"⟩ }

def errorsOf (lake : LakeFacts := baseLake) (files : FileFacts := baseFiles)
    (challenge : ChallengeFacts := baseChallenge) : Array Error :=
  (run lake files challenge).errors

def refuses (error : Error) (lake : LakeFacts := baseLake) (files : FileFacts := baseFiles)
    (challenge : ChallengeFacts := baseChallenge) : Bool :=
  (run lake files challenge).code == 1 && (run lake files challenge).errors.contains error

def duplicated : ChallengeFacts :=
  { baseChallenge with
    headlines := #[evenHeadline, againHeadline] }

def trivial : ChallengeFacts :=
  { baseChallenge with
    headlines := #[evenHeadline, trivialHeadline] }

def unkilled : ChallengeFacts :=
  { baseChallenge with
    kills := #[] }

def unmarkedKill : ChallengeFacts :=
  { baseChallenge with
    kills := #[]
    headlines := #[evenHeadline, headlineOf evenKill.target] }

def againKill : HeadlineFact :=
  headlineOf (targetOf `App.double_even_rejects_again .proved (evenStatement successor).negation 12
    "double_even_rejects_again")

def unmarkedTwice : ChallengeFacts :=
  { baseChallenge with
    kills := #[]
    headlines := #[evenHeadline, headlineOf evenKill.target, againKill] }

def duplicatedUnmarked : ChallengeFacts :=
  { baseChallenge with
    kills := #[]
    headlines := #[evenHeadline, againHeadline, headlineOf evenKill.target] }

def trivialTwice : ChallengeFacts :=
  { baseChallenge with
    headlines := #[evenHeadline, trivialHeadline, trivialAgainHeadline] }

def trivialUnreproducible : ChallengeFacts :=
  { baseChallenge with
    headlines := #[evenHeadline, { trivialHeadline with
      target.auxiliaries := #[{ constantOf (privateName "proof_1") .proved nat with isPrivate := true }] }] }

def killOfMissing : ChallengeFacts :=
  { baseChallenge with
    kills := #[{ evenKill with headline := `App.triple }] }

def unreplacedKill : ChallengeFacts :=
  { baseChallenge with
    kills := #[{ evenKill with target.constant.type := (evenStatement double).negation }] }

def misshapenKill : ChallengeFacts :=
  { baseChallenge with
    kills := #[{ evenKill with target.constant.type := (Shape.const ``False []).negation }] }

def unmentionedHole : ChallengeFacts :=
  { baseChallenge with
    holes := #[doubleHole, tripleHole] }

def codeImported : ChallengeFacts :=
  { baseChallenge with
    runtimeImports := #[specImport, codeImport]
    closure := #[`App.CoreSpec, `App.CoreCode] }

def codeReached : ChallengeFacts :=
  { baseChallenge with
    closure := #[`App.CoreSpec, `App.CoreCode] }

def toolingReached : ChallengeFacts :=
  { baseChallenge with
    closure := #[`App.CoreSpec, `Lean.Elab.Command] }

def filledChallenge : ChallengeFacts :=
  { baseChallenge with
    filled := #[(`App.helper, ⟨"Challenge.lean", 7⟩)] }

def axiomChallenge : ChallengeFacts :=
  { baseChallenge with
    axioms := #[(`App.assumed, ⟨"Challenge.lean", 7⟩)] }

def privateChallenge : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with
      target.constant.isPrivate := true
      target.constant.name := privateName "double_even" }] }

def unplainChallenge : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with target.constant.name := .str `App "1st", target.written := "«1st»" }]
    kills := #[{ evenKill with headline := .str `App "1st" }] }

def terminatesHelper : ChallengeFacts :=
  { baseChallenge with
    terminating := #[{ definition := `App.helper, headline := `App.double_even, place := ⟨"Challenge.lean", 8⟩ }] }

def terminatesMissing : ChallengeFacts :=
  { baseChallenge with
    terminating := #[{ definition := `App.double, headline := `App.missing, place := ⟨"Challenge.lean", 8⟩ }] }

def terminatesElsewhere : ChallengeFacts :=
  { baseChallenge with
    holes := #[doubleHole, tripleHole]
    headlines := #[evenHeadline, tripleHeadline]
    kills := #[evenKill, tripleKill]
    replaceable := #[`App.double, `App.triple]
    terminating := #[{ definition := `App.triple, headline := `App.double_even, place := ⟨"Challenge.lean", 8⟩ }] }

def terminatesHere : ChallengeFacts :=
  { baseChallenge with
    terminating := #[{ definition := `App.double, headline := `App.double_even, place := ⟨"Challenge.lean", 8⟩ }] }

def closedBinder : BinderFact := binderFact "h" (equal (.natLit 1) (.natLit 1)) true "1 = 1"

def closedHypothesis : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with telescope := [closedBinder] }] }

def openHypothesis : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with
      telescope := [natBinder, binderFact "h" (equal (.bvar 0) (.bvar 0)) true "n = n"] }] }

def agrees (argument : Shape) : Shape := .app (.const `App.Agrees []) argument

def claimedHypotheses : ChallengeFacts :=
  { baseChallenge with
    claims := #[`App.Agrees]
    headlines := #[{ evenHeadline with
      telescope := [binderFact "a" (agrees double) true "App.Agrees App.double",
        binderFact "b" (.forallE nat (agrees (.app double (.bvar 0)))) true "∀ m, App.Agrees (App.double m)",
        natBinder] }] }

def unclaimedBase : ChallengeFacts := { claimedHypotheses with claims := #[] }

def unclaimedHypotheses : ChallengeFacts := { unclaimedBase with witnesses := #[stated unclaimedBase (witnessOf true)] }

def dependedHypothesis : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with
      telescope := [closedBinder, binderFact "x" (.app (.const `App.Witness []) (.bvar 0)) false "App.Witness h"] }] }

def privateAuxiliary : ChallengeFacts :=
  { baseChallenge with
    headlines := #[{ evenHeadline with
      target.auxiliaries := #[{ constantOf (privateName "proof_1") .proved nat with isPrivate := true }] }] }

def holeTypedInput : HeadlineFact :=
  { evenHeadline with
    telescope := [binderFact "i" (.app (.const ``Fin []) (.app double (.natLit 2))) false "Fin (App.double 2)"] }

def declarationIn (module name : Name) : DeclarationFact :=
  { name, module, line := 4, computational := true, isUnsafe := false, isPartial := false, external := false,
    unfoldable := true, replaced := false, initializes := false, effects := false, debug := false, axioms := #[] }

def moduleNamed (name : Name) (imports : Array ImportFact := #[]) (usesModuleSystem : Bool := true) : ModuleFact :=
  { name, file := "/".intercalate (name.components.map toString) ++ ".lean", usesModuleSystem, imports }

def withOwned (owned : OwnedFacts) : ChallengeFacts := { baseChallenge with owned }

def unsafeSpec : DeclarationFact := { declarationIn `App.CoreSpec `App.CoreSpec.loop with isUnsafe := true }

def ownedImpure : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreSpec], #[unsafeSpec]⟩ }

def editableImpure : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreCode],
    #[{ declarationIn `App.CoreCode `App.CoreCode.loop with isUnsafe := true }]⟩ }

def cheatingSpec : DeclarationFact := { declarationIn `App.CoreSpec `App.CoreSpec.lemma with axioms := #[``sorryAx] }

def ownedSorry : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreSpec], #[cheatingSpec]⟩
              blames := #[{ declaration := `App.CoreSpec.lemma, axiomName := ``sorryAx, culprit := `App.CoreSpec.lemma
                            culpritModule? := some `App.CoreSpec }] }

def ownedLegacy : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreSpec (usesModuleSystem := false)], #[]⟩ }

def ownedLayering : ChallengeFacts :=
  withOwned
    { inventory := ⟨#[moduleNamed `App.CoreSpec #[{ name := `App.CoreCode, comptime := false, line := 3 }]], #[]⟩ }

def codeMetaImport : ImportFact := { name := `App.CoreCode, comptime := true, line := 3 }

def specImportsCode : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreSpec #[codeMetaImport]], #[]⟩ }

def editableImportsCode : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.Solution #[codeMetaImport]], #[]⟩ }

def claimIn (module : Name) (home? : Option Name) : RegistrationFact :=
  { claim := module ++ `Agrees, module, home?
    place := ⟨"/".intercalate (module.components.map toString) ++ ".lean", 6⟩ }

def worldLake : LakeFacts := { baseLake with modules := baseLake.modules.push ⟨`App.WorldSpec, "App/WorldSpec.lean"⟩ }

def worldFiles : FileFacts :=
  { lock := .decoded (digests.push ⟨"App/WorldSpec.lean", "5"⟩), comparator := .missing,
    digests := digests.push ⟨"App/WorldSpec.lean", "5"⟩ }

def ownedClaimOutside : ChallengeFacts := withOwned { registrations := #[claimIn `App.CoreSpec (some `App.CoreSpec)] }

def ownedClaimUnregistered : ChallengeFacts := withOwned { registrations := #[claimIn `App.WorldSpec (some `Other)] }

def ownedClaimHome : ChallengeFacts := withOwned { registrations := #[claimIn `App.WorldSpec (some `App.WorldSpec)] }

def derivedCopyIn (module : Name) : DeclarationFact :=
  { declarationIn module (module ++ `instBEqTree) with
    isPartial := true, written := false, copyOf := some (module ++ `instBEqTree.beq), copyOfInstanceMethod := true }

def derivedSpec : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreSpec], #[derivedCopyIn `App.CoreSpec]⟩ }

def derivedCode : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreCode], #[derivedCopyIn `App.CoreCode]⟩ }

def totalCopySpec : ChallengeFacts :=
  withOwned { inventory := ⟨#[moduleNamed `App.CoreSpec],
    #[{ derivedCopyIn `App.CoreSpec with copyOfTotal := true }]⟩ }

def reachedThrough : ChallengeFacts :=
  { codeReached with
    imports := #[(`App.CoreSpec, #[`App.CoreSpec.Helpers]), (`App.CoreSpec.Helpers, #[`App.CoreCode])] }

def unwitnessed : ChallengeFacts :=
  { baseChallenge with
    headlines := #[holeTypedInput] }

def witnessedInput : ChallengeFacts := { baseChallenge with headlines := #[holeTypedInput] }

def witnessed : ChallengeFacts := { witnessedInput with witnesses := #[stated witnessedInput (witnessOf true)] }

def unwitnessedUnkilled : ChallengeFacts :=
  { baseChallenge with
    headlines := #[holeTypedInput]
    kills := #[] }

def predeclared : ChallengeFacts :=
  { baseChallenge with
    witnesses := #[witnessOf false] }

def twoChallenges : LakeFacts :=
  { baseLake with
    challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩, ⟨`App.Challenge, "App/Challenge.lean"⟩] }

def otherChallenge : LakeFacts :=
  { baseLake with
    challengeCandidates := #[⟨`App.Challenge, "App/Challenge.lean"⟩] }

def noSolution : LakeFacts :=
  { baseLake with
    modules := #[⟨`App.CoreSpec, "App/CoreSpec.lean"⟩] }

def twoSolutions : LakeFacts :=
  { baseLake with
    modules := baseLake.modules.push ⟨`Other.Solution, "Other/Solution.lean"⟩ }

def repeatedSolution : LakeFacts :=
  { baseLake with
    modules := baseLake.modules.push ⟨`App.Solution, "App/Solution.lean"⟩ }

def toolingRoot : LakeFacts :=
  { baseLake with
    modules := baseLake.modules.push ⟨`App.WorldCode, "App/WorldCode.lean"⟩
    defaultExeRoots := #[`Main] }

def worldRoot : LakeFacts :=
  { toolingRoot with
    defaultExeRoots := #[`Main, `App.WorldCode] }

def witnessedHeadline : HeadlineFact :=
  { evenHeadline with telescope := [{ natBinder with level := .succ .zero },
      binderFact "h" (equal (.app double (.bvar 0)) (.natLit 0)) true "App.double n = 0"] }

def witnessedBase : ChallengeFacts := { baseChallenge with headlines := #[witnessedHeadline] }

def misstatedWitness : ChallengeFacts := { witnessedBase with witnesses := #[witnessOf true] }

def statedWitness : ChallengeFacts := { witnessedBase with witnesses := #[stated witnessedBase (witnessOf true)] }

end

#guard (run baseLake baseFiles baseChallenge).code == 0

#guard errorsOf == #[]

#guard (run baseLake baseFiles baseChallenge).writes.config? == some
  { challenge := `Challenge, solution := `App.Solution, theorems := #[`App.double_even, `App.double_even_rejects],
    definitions := #[`App.double], axioms := standardAxioms }

#guard (run baseLake baseFiles baseChallenge).writes.lock? == none

#guard (run baseLake { baseFiles with lock := .missing } baseChallenge).writes.lock? == some digests

#guard (run baseLake baseFiles unkilled).writes == { lock? := none, config? := none }

#guard plain `App.double && !plain (.str `App "1st") && !plain (.num `App 0) && !plain .anonymous &&
  !plain (.str `App "a.b") && !plain (.str `App "") && plain (.str `App "with space")

#guard (evenStatement double).constants == [``Nat, `App.Even, `App.double]

#guard killedBy (· == `App.double) (evenStatement double) [] (evenStatement successor).negation

#guard !killedBy (· == `App.double) (evenStatement double) [] (evenStatement double).negation

#guard !killedBy (· == `App.double) (evenStatement double) [] (evenStatement (.bvar 0)).negation

#guard killedBy (· == `App.double) (evenStatement double) [even (.app double (.natLit 1))]
  (Shape.conjunction [(evenStatement successor).negation, even (.app successor (.natLit 1))])

#guard !killedBy (· == `App.double) (evenStatement double) [even (.app double (.natLit 1))]
  (Shape.conjunction [(evenStatement successor).negation, even (.app double (.natLit 1))])

#guard !killedBy (· == `App.double) (evenStatement double) []
  (Shape.conjunction [(evenStatement successor).negation, even (.app successor (.natLit 1))])

#guard killedBy (fun name => name == `App.double || name == ``And) (evenStatement double)
  [even (.app double (.natLit 1))]
  (Shape.conjunction [(evenStatement successor).negation, even (.app successor (.natLit 1))])

#guard refuses (.duplicate `App.double_even_again `App.double_even) (challenge := duplicated)

#guard !(errorsOf (challenge := duplicated)).contains (.noKill `App.double_even_again (some template))

#guard refuses (.mentionsNothing `App.trivial) (challenge := trivial)

#guard !(errorsOf (challenge := trivial)).any (· matches .noKill _ _)

#guard refuses (.noKill `App.double_even (some template)) (challenge := unkilled)

#guard refuses (.unmarkedKill `App.double_even `App.double_even_rejects) (challenge := unmarkedKill)

#guard errorsOf (challenge := unmarkedKill) == #[.unmarkedKill `App.double_even `App.double_even_rejects]

#guard errorsOf (challenge := unmarkedTwice) ==
  #[.duplicate `App.double_even_rejects_again `App.double_even_rejects,
    .unmarkedKill `App.double_even `App.double_even_rejects]

#guard errorsOf (challenge := duplicatedUnmarked) ==
  #[.duplicate `App.double_even_again `App.double_even, .unmarkedKill `App.double_even `App.double_even_rejects]

#guard errorsOf (challenge := trivialTwice) ==
  #[.duplicate `App.trivial_again `App.trivial, .mentionsNothing `App.trivial]

#guard errorsOf (challenge := trivialUnreproducible) == #[.privateAuxiliary `App.trivial (privateName "proof_1")]

#guard refuses (.killOfNonHeadline `App.double_even_rejects `App.triple) (challenge := killOfMissing)

#guard refuses (.killReplacesNothing `App.double_even_rejects `App.double_even) (challenge := unreplacedKill)

#guard refuses (.misshapenKill `App.double_even_rejects `App.double_even) (challenge := misshapenKill)

#guard refuses (.unmentionedHole `App.triple) (challenge := unmentionedHole)

#guard refuses (.challengeImport codeImport (some .coreCode)) (files := codeFiles) (challenge := codeImported)

#guard !(errorsOf (files := codeFiles) (challenge := codeImported)).contains (.codeInClosure `App.CoreCode)

#guard refuses (.codeInClosure `App.CoreCode) (files := codeFiles) (challenge := codeReached)

#guard refuses (.ownedUnread "App/CoreCode.lean") (challenge := codeReached)

#guard errorsOf (challenge := toolingReached) == #[]

#guard refuses (.filled `App.helper) (challenge := filledChallenge)

#guard refuses (.challengeAxiom `App.assumed) (challenge := axiomChallenge)

#guard refuses (.privateTarget (privateName "double_even")) (challenge := privateChallenge)

#guard !(errorsOf (challenge := privateChallenge)).any (· matches .unplainName _)

#guard refuses (.unplainName (.str `App "1st")) (challenge := unplainChallenge)

#guard refuses (.terminatesNotHole `App.double_even `App.helper) (challenge := terminatesHelper)

#guard refuses (.terminatesWithoutKill `App.missing `App.double) (challenge := terminatesMissing)

#guard refuses (.terminatesUnmentioned `App.double_even `App.triple) (challenge := terminatesElsewhere)

#guard errorsOf (challenge := terminatesHere) == #[]

#guard refuses (.unnamedHypothesis `App.double_even closedBinder) (challenge := closedHypothesis)

#guard errorsOf (challenge := openHypothesis) == #[]

#guard errorsOf (challenge := claimedHypotheses) == #[]

#guard (errorsOf (challenge := unclaimedHypotheses)).size == 2

#guard (errorsOf (challenge := unclaimedHypotheses)).all (· matches .unnamedHypothesis `App.double_even _)

#guard errorsOf (challenge := dependedHypothesis) == #[]

#guard ((claimedHypotheses.headlines[0]!).binders claimedHypotheses).map (·.kind) == [.claim, .claim, .input]

#guard ((unclaimedHypotheses.headlines[0]!).binders unclaimedHypotheses).map (·.kind) ==
  [.precondition, .precondition, .input]

#guard ((dependedHypothesis.headlines[0]!).binders dependedHypothesis).map
  (fun binder => (binder.kind, binder.refers)) == [(.input, []), (.input, [0])]

#guard (claimedHypotheses.headlines[0]!).claimed claimedHypotheses ==
  #[(0, `App.Agrees, "App.Agrees App.double"), (1, `App.Agrees, "∀ m, App.Agrees (App.double m)")]

#guard (holeTypedInput.binders baseChallenge).map (·.mentions) == [true]

#guard needsWitness baseChallenge holeTypedInput && !needsWitness claimedHypotheses (claimedHypotheses.headlines[0]!)

#guard refuses (.ownedViolation (.impure `App.CoreSpec.loop .coreSpec [.«unsafe»])) (challenge := ownedImpure)

#guard errorsOf (challenge := editableImpure) == #[]

#guard refuses (.ownedViolation (.axioms `App.CoreSpec.lemma #[``sorryAx])) (challenge := ownedSorry)

#guard refuses (.ownedViolation (.legacy `App.CoreSpec)) (challenge := ownedLegacy)

#guard refuses (.ownedViolation (.forbiddenImport `App.CoreSpec `App.CoreCode .coreSpec)) (challenge := ownedLayering)

#guard errorsOf (challenge := ownedLayering) == #[.ownedViolation (.forbiddenImport `App.CoreSpec `App.CoreCode .coreSpec)]

#guard refuses (.specImport `App.CoreSpec codeMetaImport) (challenge := specImportsCode)

#guard errorsOf (challenge := specImportsCode) == #[.specImport `App.CoreSpec codeMetaImport]

#guard errorsOf (challenge := editableImportsCode) == #[]

#guard refuses (.ownedClaim (claimIn `App.CoreSpec (some `App.CoreSpec))) (challenge := ownedClaimOutside)

#guard refuses (.ownedClaim (claimIn `App.WorldSpec (some `Other))) (lake := worldLake) (files := worldFiles)
  (challenge := ownedClaimUnregistered)

#guard errorsOf (lake := worldLake) (files := worldFiles) (challenge := ownedClaimHome) == #[]

#guard refuses (.derivedPartial `App.CoreSpec.instBEqTree `App.CoreSpec) (challenge := derivedSpec)

#guard errorsOf (challenge := derivedSpec) == #[.derivedPartial `App.CoreSpec.instBEqTree `App.CoreSpec]

#guard errorsOf (challenge := derivedCode) == #[]

#guard errorsOf (challenge := totalCopySpec) == #[]

#guard refuses (.privateAuxiliary `App.double_even (privateName "proof_1")) (challenge := privateAuxiliary)

#guard setupOf { baseLake with lintDriver := "" } == #[.lintDriver ""]

#guard setupOf { baseLake with testDriver := "" } == #[.testDriver ""]

#guard setupOf { baseLake with builtinLint := some ⟨"lakefile.lean", 5⟩ } == #[.builtinLint ⟨"lakefile.lean", 5⟩]

#guard setupOf baseLake == #[]

#guard refuses (.witnessMisstated `App.double_even_applies `App.double_even) (challenge := misstatedWitness)

#guard !(errorsOf (challenge := statedWitness)).any (· matches .witnessMisstated ..)

#guard witnessedHeadline.expectedWitness witnessedBase ==
  .app (.app (.const ``Exists [.succ .zero]) (.const ``Nat []))
    (.lam (.const ``Nat []) (equal (.app double (.bvar 0)) (.natLit 0)))

#guard refuses (.witnessMissing `App.double_even) (challenge := unwitnessed)

#guard errorsOf (challenge := witnessed) == #[]

#guard !(errorsOf (challenge := unwitnessedUnkilled)).contains (.witnessMissing `App.double_even)

#guard refuses (.witnessPredeclared `App.double_even_applies `App.double_even) (challenge := predeclared)

#guard refuses (.challengeLookup #[]) (lake := { baseLake with challengeCandidates := #[] })

#guard errorsOf (lake := { baseLake with challengeCandidates := #[] })
  (files := { baseFiles with lock := .unreadable "expected an object" })
  (challenge := { baseChallenge with file := "", kills := #[] }) == #[.challengeLookup #[]]

#guard refuses (.challengeLookup twoChallenges.challengeCandidates) (lake := twoChallenges)

#guard refuses (.challengeAbsent `App.Challenge "App/Challenge.lean") (lake := otherChallenge)

#guard refuses (.solutionModule #[]) (lake := noSolution)

#guard refuses (.solutionModule #[`App.Solution, `Other.Solution]) (lake := twoSolutions)

#guard errorsOf (lake := repeatedSolution) == #[]

#guard refuses .noStatementTarget (lake := { baseLake with defaultTargets := #[] })

#guard refuses (.exeRootsOutsideWorldCode #[`Main]) (lake := toolingRoot)

#guard errorsOf (lake := { baseLake with defaultExeRoots := #[`Main] }) == #[]

#guard errorsOf (lake := worldRoot) == #[]

#guard refuses (.ownedUnread "App/CoreSpec.lean")
  (files := { baseFiles with lock := .missing, digests := digests.pop })

#guard errorsOf (files := { baseFiles with digests := digests.pop }) ==
  #[.lock (.missing "App/CoreSpec.lean") (some (.specModule `App.CoreSpec))]

#guard refuses (.lock (.differs "Challenge.lean") (some .challenge))
  (files := { baseFiles with digests := changedDigests })

#guard refuses (.lock (.unrecorded "App/CoreSpec.lean") (some (.specModule `App.CoreSpec)))
  (files := { baseFiles with lock := .decoded digests.pop })

#guard refuses (.lock (.unrecorded "App/Solution.lean") none)
  (files := { baseFiles with digests := digests.push ⟨"App/Solution.lean", "5"⟩ })

#guard refuses (.lock (.missing "Gone.lean") none)
  (files := { baseFiles with lock := .decoded (digests.push ⟨"Gone.lean", "4"⟩) })

#guard refuses (.lockUnreadable "expected an object")
  (files := { baseFiles with lock := .unreadable "expected an object" })

#guard errorsOf (files := { baseFiles with lock := .decoded changedDigests }) (challenge := unkilled) ==
  #[.lock (.differs "Challenge.lean") (some .challenge)]

#guard errorsOf (lake := noSolution) (files := { baseFiles with lock := .decoded changedDigests }) ==
  #[.lock (.differs "Challenge.lean") (some .challenge), .solutionModule #[]]

end SoftwareChallengeTests.Rules.Statement

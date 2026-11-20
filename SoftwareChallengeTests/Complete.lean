module

import SoftwareChallenge.CoreSpec.Lint
import SoftwareChallenge.CoreSpec.Test
meta import SoftwareChallenge.CoreSpec.Role

namespace SoftwareChallengeTests.Complete

open Lean SoftwareChallenge

def completeLake : LakeFacts :=
  { packageDir := "/work", configFiles := #["lakefile.lean"],
    modules := #[⟨`App.Solution, "App/Solution.lean"⟩], challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩],
    defaultExeRoots := #[], packages := #[], defaultTargets := #[`statement], builtinLint := none, testDriver := "software_challenge/test_challenge",
    testDriverArgs := #[], testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, ownTests := #[], inputs := #[] }

def completeChallenge : ChallengeFacts :=
  { module := `Challenge, file := "Challenge.lean", runtimeImports := #[], metaImports := #[], closure := #[],
    headlines := #[], kills := #[], witnesses := #[], holes := #[], filled := #[], axioms := #[], terminating := #[],
    replaceable := #[] }

def digested : Array Lock.Entry :=
  #[⟨"lakefile.lean", "1"⟩, ⟨"Challenge.lean", "2"⟩, ⟨"App/Solution.lean", "3"⟩]

def completeFiles : FileFacts :=
  { lock := .decoded digested, digests := digested,
    comparator := .decoded (Config.expected completeChallenge `App.Solution) }

def solutionModule : ModuleFact :=
  { name := `App.Solution, file := "App/Solution.lean", usesModuleSystem := true, imports := #[] }

def completeSolution : SolutionFacts :=
  { solution? := some `App.Solution, inventory := ⟨#[solutionModule], #[]⟩, blames := #[], imports := #[],
    calls := #[], proofUses := #[], meanings := #[], found := #[], solutionClosure := #[], importsSolution := #[],
    premiseUses := #[], claimUses := #[], checks := #[], registrations := #[], lints := #[],
    linted := #[`App.Solution], sorries := #[], fixpoints := #[], main? := none, places := #[] }

def completeFacts : Facts :=
  { lake := completeLake, files := completeFiles, challenge := completeChallenge, solution := completeSolution }

def completeTests : TestFacts :=
  { declaredChecks := #[], checks := #[], declaredOwnTests := #[], ownTests := #[], unknownOwnTests := #[],
    testDriverArgsPlace := ⟨"lakefile.lean", 9⟩, libraryPlace := ⟨"lakefile.lean", 14⟩ }

theorem completeOwnedDigested (path : String) (owned : completeLake.Owned completeChallenge path) :
    completeFiles.Digested path := by
  rcases owned with listed | named | ⟨source, listed, -, filed⟩
  · simp [completeLake] at listed
    exact ⟨⟨"lakefile.lean", "1"⟩, by simp [completeFiles, digested], listed.symm⟩
  · exact ⟨⟨"Challenge.lean", "2"⟩, by simp [completeFiles, digested], named.symm⟩
  · simp [completeLake] at listed
    subst listed
    exact ⟨⟨"App/Solution.lean", "3"⟩, by simp [completeFiles, digested], filed⟩

theorem completeOneSolution : completeLake.OneSolution :=
  ⟨⟨`App.Solution, "App/Solution.lean"⟩, by simp [completeLake], rfl, fun other member _ => by
    simp [completeLake] at member; simp [member]⟩

theorem statementComplete : Statement.Complete completeLake completeFiles completeChallenge where
  challengeFound := ⟨⟨`Challenge, "Challenge.lean"⟩, rfl, rfl⟩
  oneSolution := completeOneSolution
  statementTarget := by simp [completeLake]
  programRooted := fun nonempty => absurd rfl nonempty
  importsOnlySpecs := by simp [completeChallenge]
  closureHoldsNoCode := by simp [completeChallenge]
  declaresOnlyTheoremsAndHoles := rfl
  assumesNoAxiom := rfl
  targetsPublic := by simp [completeChallenge, ChallengeFacts.targets, ChallengeFacts.theorems]
  namesPlain := by simp [completeChallenge, ChallengeFacts.targets, ChallengeFacts.theorems]
  auxiliariesPublic := by simp [completeChallenge, ChallengeFacts.targets, ChallengeFacts.theorems]
  headlinesMentionHoles := by simp [completeChallenge]
  headlinesKilled := by simp [completeChallenge]
  killsNameHeadlines := by simp [completeChallenge]
  killsReject := by simp [completeChallenge]
  killsMarked := by simp [completeChallenge]
  headlinesDistinct := by simp [completeChallenge]
  holesMentioned := by simp [completeChallenge]
  hypothesesClaimed := by simp [completeChallenge]
  preconditionsWitnessed := by simp [completeChallenge]
  witnessesDerived := by simp [completeChallenge]
  witnessesStated := by simp [completeChallenge]
  terminatesNamesHole := by simp [completeChallenge]
  terminatesOnKilledHeadline := by simp [completeChallenge]
  terminatesMentionsHole := by simp [completeChallenge]
  ownedAdmitted := {
    placed := by simp [completeChallenge, Inventory.restrictedTo]
    modular := by simp [completeChallenge, Inventory.restrictedTo]
    layered := by simp [completeChallenge, Inventory.restrictedTo]
    pure := by simp [completeChallenge, Inventory.restrictedTo] }
  specImportsOwned := by simp [completeChallenge]
  ownedClaimsDeclared := by simp [completeChallenge]
  ownedDerivedTotal := by simp [completeChallenge]
  ownedDigested := completeOwnedDigested
  lockCurrent := .inr ⟨digested, rfl, fun _ => rfl⟩

theorem lintComplete : Lint.Complete completeFacts where
  modulesAudited := fun source member _ => by
    simp [completeFacts, completeLake] at member
    subst member
    exact ⟨solutionModule, by simp [completeFacts, completeSolution], rfl⟩
  exeRootsAudited := by simp [completeFacts, completeLake]
  lintersCover := by simp [completeFacts, completeSolution, solutionModule]
  lintersPass := rfl
  noSorry := rfl
  admitted := {
    placed := fun fact member => by
      simp [completeFacts, completeSolution] at member
      subst member
      exact ⟨_, by simp [Project.role?, LakeFacts.project, completeFacts, completeLake, solutionModule]; rfl⟩
    modular := by simp [completeFacts, completeSolution, solutionModule]
    layered := by simp [completeFacts, completeSolution, solutionModule]
    pure := by simp [completeFacts, completeSolution] }
  specMetaImportsOwned := by simp [completeFacts, completeSolution, solutionModule]
  declaredOnce := by simp [completeFacts, completeSolution]
  holesInCode := by simp [completeFacts, completeChallenge]
  holesCompiled := by simp [completeFacts, completeChallenge]
  mainInWorldCode := fun _ main found => by simp [completeFacts, completeSolution] at found
  fixpointsDeclared := by simp [completeFacts, completeChallenge]
  fixpointsTerminate := by simp [completeFacts, completeChallenge]
  claimsDeclared := by simp [completeFacts, completeSolution]
  proofsReadable := by simp [completeFacts, completeChallenge]
  ownedDigested := completeOwnedDigested
  lockCurrent := ⟨digested, rfl, fun _ => rfl⟩
  comparatorCurrent := ⟨⟨`App.Solution, "App/Solution.lean"⟩, by simp [completeFacts, completeLake], rfl, rfl⟩
  oneSolution := completeOneSolution
  statementTarget := by simp [completeFacts, completeLake]
  challengeUnimported := by simp [completeFacts, completeSolution]
  builtinLintOff := rfl
  headlinesProved := by simp [completeFacts, completeChallenge]
  holesDefined := by simp [completeFacts, completeChallenge]
  killsProved := by simp [completeFacts, completeChallenge]
  witnessesProved := by simp [completeFacts, completeChallenge]
  mainReachesHoles := fun ⟨root, member, _⟩ => by simp [completeFacts, completeLake] at member
  claimsChecked := by simp [completeFacts, completeChallenge]
  checksDecided := by simp [completeFacts, completeSolution]
  dependenciesVisible := by simp [completeFacts, completeLake]

theorem testsComplete : Test.Complete completeTests where
  checksRun := by simp [completeTests]
  checksPass := by simp [completeTests]
  ownTestsRun := by simp [completeTests]
  ownTestsPass := by simp [completeTests]
  ownTestsDeclared := rfl

def unauditedModule : Facts :=
  { completeFacts with
    lake := { completeLake with modules := completeLake.modules.push ⟨`App.Extra, "App/Extra.lean"⟩ } }

theorem unauditedModule_unclean : ¬ Lint.Clean unauditedModule := fun clean => by
  obtain ⟨fact, member, named⟩ := clean.modulesAudited ⟨`App.Extra, "App/Extra.lean"⟩
    (by simp [unauditedModule, completeLake]) (by simp [unauditedModule, completeFacts, completeChallenge])
  simp [unauditedModule, completeFacts, completeSolution] at member
  subst member
  simp [solutionModule] at named

def unauditedExeRoot : Facts := { completeFacts with lake := { completeLake with defaultExeRoots := #[`Main] } }

theorem unauditedExeRoot_unclean : ¬ Lint.Clean unauditedExeRoot := fun clean => by
  obtain ⟨fact, member, named⟩ := clean.exeRootsAudited `Main (by simp [unauditedExeRoot])
  simp [unauditedExeRoot, completeFacts, completeSolution] at member
  subst member
  simp [solutionModule] at named

def unlinted : Facts := { completeFacts with solution := { completeSolution with linted := #[] } }

theorem unlinted_unclean : ¬ Lint.Clean unlinted := fun clean => by
  have covered := clean.lintersCover solutionModule (by simp [unlinted, completeSolution])
  simp [unlinted] at covered

def tacticLake : LakeFacts :=
  { completeLake with modules := completeLake.modules.push ⟨`App.Tactic, "App/Tactic.lean"⟩ }

def tacticChallenge : ChallengeFacts := { completeChallenge with closure := #[`App.Tactic] }

theorem tacticOwned : tacticLake.Owned tacticChallenge "App/Tactic.lean" :=
  Or.inr (Or.inr ⟨⟨`App.Tactic, "App/Tactic.lean"⟩, by simp [tacticLake, completeLake],
    Or.inl (by simp [tacticChallenge]), rfl⟩)

theorem tacticUndigested : ¬ completeFiles.Digested "App/Tactic.lean" := fun ⟨entry, member, named⟩ => by
  simp [completeFiles, digested] at member
  rcases member with rfl | rfl | rfl <;> simp at named

theorem closureUndigested_incomplete : ¬ Statement.Complete tacticLake completeFiles tacticChallenge :=
  fun complete => tacticUndigested (complete.ownedDigested _ tacticOwned)

def closureUndigested : Facts := { completeFacts with lake := tacticLake, challenge := tacticChallenge }

theorem closureUndigested_unclean : ¬ Lint.Clean closureUndigested :=
  fun clean => tacticUndigested (clean.ownedDigested _ tacticOwned)

def specModule : ModuleFact :=
  { name := `App.CoreSpec.Defs, file := "App/CoreSpec/Defs.lean", usesModuleSystem := true,
    imports := #[{ name := `App.CoreCode.Impl, comptime := true, line := 3 }] }

def metaImportsCode : Facts :=
  { completeFacts with
    lake := { completeLake with
      modules := completeLake.modules ++ #[⟨`App.CoreSpec.Defs, "App/CoreSpec/Defs.lean"⟩,
        ⟨`App.CoreCode.Impl, "App/CoreCode/Impl.lean"⟩] }
    solution := { completeSolution with inventory := ⟨#[solutionModule, specModule], #[]⟩ } }

#guard Role.ofName `App.CoreSpec.Defs == .coreSpec
#guard Role.ofName `App.CoreCode.Impl == .coreCode

theorem metaImportsCode_unclean (spec : (Role.ofName `App.CoreSpec.Defs).Owned)
    (code : Role.ofName `App.CoreCode.Impl = .coreCode) : ¬ Lint.Clean metaImportsCode := fun clean => by
  have owns := clean.specMetaImportsOwned specModule (by simp [metaImportsCode, completeSolution]) spec
    { name := `App.CoreCode.Impl, comptime := true, line := 3 } (by simp [specModule]) rfl
    ⟨⟨`App.CoreCode.Impl, "App/CoreCode/Impl.lean"⟩, by simp [metaImportsCode, completeLake], rfl⟩
  rcases owns with closed | owned
  · simp [metaImportsCode, completeFacts, completeChallenge] at closed
  · rw [code] at owned
    simp [Role.Owned] at owned

def toolingExeLake : LakeFacts :=
  { completeLake with modules := completeLake.modules.push ⟨`App.WorldCode, "App/WorldCode.lean"⟩,
                      defaultExeRoots := #[`Main] }

#guard Role.ofName `App.WorldCode == .worldCode
#guard Role.ofName `Main == .tooling

theorem toolingExe_incomplete (world : Role.ofName `App.WorldCode = .worldCode)
    (tooling : Role.ofName `Main = .tooling) : ¬ Statement.Complete toolingExeLake completeFiles completeChallenge :=
  fun complete => by
    obtain ⟨root, member, rooted⟩ := complete.programRooted (by simp [toolingExeLake])
      ⟨⟨`App.WorldCode, "App/WorldCode.lean"⟩, by simp [toolingExeLake, completeLake], world⟩
    simp [toolingExeLake] at member
    subst member
    rw [tooling] at rooted
    cases rooted

def impureSpec : DeclarationFact :=
  { name := `App.CoreSpec.loop, module := `App.CoreSpec, line := 4, computational := true, isUnsafe := false,
    isPartial := true, external := false, unfoldable := true, replaced := false, initializes := false,
    effects := false, debug := false, axioms := #[] }

def specModuleFact (imports : Array ImportFact) : ModuleFact :=
  { name := `App.CoreSpec, file := "App/CoreSpec.lean", usesModuleSystem := true, imports }

def impureSpecOwned : OwnedFacts := { inventory := ⟨#[specModuleFact #[]], #[impureSpec]⟩ }

def impureSpecChallenge : ChallengeFacts := { completeChallenge with owned := impureSpecOwned }

def impureSpecLake : LakeFacts :=
  { completeLake with modules := completeLake.modules.push ⟨`App.CoreSpec, "App/CoreSpec.lean"⟩ }

#guard Role.ofName `App.CoreSpec == .coreSpec

theorem impureSpec_incomplete (spec : Role.ofName `App.CoreSpec = .coreSpec) :
    ¬ Statement.Complete impureSpecLake completeFiles impureSpecChallenge := fun complete => by
  have kept :
      impureSpec ∈ (impureSpecChallenge.owned.inventory.restrictedTo impureSpecChallenge.owns).declarations := by
    simp [impureSpecChallenge, impureSpecOwned, Inventory.restrictedTo, ChallengeFacts.owns, impureSpec, spec]
  obtain ⟨role, classified, -, allowed⟩ := complete.ownedAdmitted.pure impureSpec kept
  have placed : role = .coreSpec := by
    simp [Project.role?, LakeFacts.project, impureSpecLake, completeLake, impureSpec, spec] at classified
    exact classified.symm
  subst placed
  simp [DeclarationFact.Allowed, DeclarationFact.countsAsPartial, DeclarationFact.compilerCopy, impureSpec] at allowed

def misplacedClaim : RegistrationFact :=
  { claim := `App.CoreSpec.Agrees, module := `App.CoreSpec, home? := some `App.CoreSpec,
    place := ⟨"App/CoreSpec.lean", 6⟩ }

def misplacedClaimChallenge : ChallengeFacts :=
  { completeChallenge with owned := { registrations := #[misplacedClaim] } }

theorem misplacedClaim_incomplete (spec : Role.ofName `App.CoreSpec = .coreSpec) :
    ¬ Statement.Complete impureSpecLake completeFiles misplacedClaimChallenge := fun complete => by
  have declared := complete.ownedClaimsDeclared misplacedClaim (by simp [misplacedClaimChallenge])
    (Or.inr (Or.inl spec))
  simp [Project.role?, LakeFacts.project, impureSpecLake, completeLake, misplacedClaim, spec] at declared

def derivedInstance : DeclarationFact :=
  { impureSpec with name := `App.CoreSpec.instBEqTree, written := false, copyOf := some `App.CoreSpec.instBEqTree.beq,
                    copyOfInstanceMethod := true }

def derivedChallenge : ChallengeFacts :=
  { completeChallenge with owned := { inventory := ⟨#[specModuleFact #[]], #[derivedInstance]⟩ } }

theorem derived_incomplete (spec : Role.ofName `App.CoreSpec = .coreSpec) :
    ¬ Statement.Complete impureSpecLake completeFiles derivedChallenge := fun complete =>
  complete.ownedDerivedTotal derivedInstance (by simp [derivedChallenge]) rfl (Or.inr (Or.inl spec))

def editableSpecImport : ChallengeFacts :=
  { completeChallenge with
    owned := { inventory := ⟨#[specModuleFact #[{ name := `App.Tactic, comptime := true, line := 3 }]], #[]⟩ } }

theorem editableSpecImport_incomplete (spec : Role.ofName `App.CoreSpec = .coreSpec)
    (tooling : Role.ofName `App.Tactic = .tooling) :
    ¬ Statement.Complete tacticLake completeFiles editableSpecImport := fun complete => by
  have owned := complete.specImportsOwned (specModuleFact #[{ name := `App.Tactic, comptime := true, line := 3 }])
    (by simp [editableSpecImport]) (Or.inl spec) { name := `App.Tactic, comptime := true, line := 3 }
    (by simp [specModuleFact]) rfl
    ⟨⟨`App.Tactic, "App/Tactic.lean"⟩, by simp [tacticLake, completeLake], rfl⟩
  rcases owned with closed | owned
  · simp [editableSpecImport, completeChallenge] at closed
  · rw [tooling] at owned
    simp [Role.Owned] at owned

#guard Role.ofName `App.Tactic == .tooling

def declaredCheck : CheckFact :=
  { claim := `App.WorldSpec.Agrees, statement := "Agrees 1", place := ⟨"App/WorldCode.lean", 9⟩ }

def checkNotRun : TestFacts := { completeTests with declaredChecks := #[declaredCheck] }

theorem checkNotRun_incomplete : ¬ Test.Complete checkNotRun := fun complete => by
  obtain ⟨outcome, member, -⟩ := complete.checksRun declaredCheck (by simp [checkNotRun])
  simp [checkNotRun, completeTests] at member

def declaredOwnTest : OwnTestFact := { name := "own", kind := .script, place := ⟨"lakefile.lean", 7⟩ }

def ownTestNotRun : TestFacts := { completeTests with declaredOwnTests := #[declaredOwnTest] }

theorem ownTestNotRun_incomplete : ¬ Test.Complete ownTestNotRun := fun complete => by
  obtain ⟨run, member, -⟩ := complete.ownTestsRun declaredOwnTest (by simp [ownTestNotRun])
  simp [ownTestNotRun, completeTests] at member

end SoftwareChallengeTests.Complete

module

public meta import SoftwareChallengeTests.Rules.LintFacts

public section

namespace SoftwareChallengeTests.Rules.Lint

open Lean SoftwareChallenge SoftwareChallengeTests.Rules.LintFacts

meta section

#guard (Lint.run complete).code == 0

def rejects (facts : Facts) (expected : Lint.Error → Bool) : Bool :=
  (Lint.run facts).code == 1 && (errorsOf facts).any expected

def pends (facts : Facts) (expected : Lint.Pending → Bool) : Bool :=
  (Lint.run facts).code == 2 && (errorsOf facts).isEmpty && (pendingOf facts).any expected

def unbuiltRoot : Facts := withLake fun lake => { lake with defaultExeRoots := lake.defaultExeRoots.push `App.Tool }

#guard rejects unbuiltRoot (· matches .unaudited `App.Tool)

def unreadModule : Facts := withLake fun lake => { lake with modules := lake.modules.push (source `App.Extra "App/Extra.lean") }

#guard rejects unreadModule (· matches .unaudited `App.Extra)

def unlinted : Facts := withSolution fun solution => { solution with linted := #[`App.CoreSpec] }

#guard rejects unlinted (· matches .unlinted `App.CoreCode)

def metaCode : ImportFact := { name := `App.CoreCode, comptime := true, line := 4 }

def withModule (name : Name) (change : ModuleFact → ModuleFact) : Facts := withSolution fun solution =>
  { solution with inventory := { solution.inventory with
      modules := solution.inventory.modules.map fun fact => if fact.name == name then change fact else fact } }

def specImportsCode : Facts := withModule `App.CoreSpec fun fact => { fact with imports := fact.imports.push metaCode }

#guard rejects specImportsCode fun
  | .metaImportsEditable `App.CoreSpec dependency => dependency.name == `App.CoreCode
  | _ => false

def legacy : Facts := withModule `App.CoreCode ({ · with usesModuleSystem := false })

#guard rejects legacy (· matches .violation (.legacy `App.CoreCode))

def codeImportsWorld : Facts :=
  withModule `App.CoreCode fun fact => { fact with imports := fact.imports.push (runtime `App.WorldCode 4) }

#guard rejects codeImportsWorld (· matches .violation (.forbiddenImport `App.CoreCode `App.WorldCode .coreCode))

def unplaced : Facts := withSolution fun solution =>
  { solution with inventory := { solution.inventory with
      modules := solution.inventory.modules.push (moduleFact `App.Stray "App/Stray.lean" #[]) } }

#guard rejects unplaced (· matches .violation (.unplaced `App.Stray))

def withDeclaration (change : DeclarationFact → DeclarationFact) (name : Name) : Facts :=
  withSolution fun solution => { solution with inventory := { solution.inventory with
    declarations := solution.inventory.declarations.map fun fact => if fact.name == name then change fact else fact } }

def unsafeCode : Facts := withDeclaration ({ · with isUnsafe := true }) `App.fold

#guard rejects unsafeCode (· matches .violation (.impure `App.fold .coreCode [.«unsafe»]))

def sorryInLemma : Facts := withDeclaration ({ · with axioms := #[``sorryAx] }) `App.fold_lemma

#guard rejects sorryInLemma (· matches .violation (.axioms `App.fold_lemma _))

def blame (declaration culprit : Name) (module : Name) : AxiomBlame :=
  { declaration, axiomName := ``sorryAx, culprit, culpritModule? := some module }

def blamed : Facts :=
  let sorried := withDeclaration ({ · with axioms := #[``sorryAx] }) `App.fold_correct
  { sorried with solution := { sorried.solution with
    blames := #[blame `App.fold_correct `App.fold_lemma `App.Solution] } }

#guard rejects blamed (· matches .axiomUse { declaration := `App.fold_correct, .. })

def chained : Facts :=
  let sorried := fun (fact : DeclarationFact) =>
    if fact.name == `App.fold_lemma || fact.name == `App.run then { fact with axioms := #[``sorryAx] } else fact
  withSolution fun solution => { solution with
    inventory := { solution.inventory with declarations := solution.inventory.declarations.map sorried }
    blames := #[blame `App.fold_lemma ``sorryAx `Init, blame `App.run `App.fold_lemma `App.Solution] }

#guard (errorsOf chained).any (· matches .violation (.axioms `App.fold_lemma _) | .axiomUse { declaration := `App.fold_lemma, .. })
#guard !(errorsOf chained).any (· matches .axiomUse { declaration := `App.run, .. })

def unsafeType : Facts := withSolution fun solution => { solution with
  inventory := { solution.inventory with declarations := solution.inventory.declarations ++
    #[{ declaration `App.Tree `App.CoreCode 30 true with isUnsafe := true },
      { declaration `App.Tree.casesOn `App.CoreCode 0 true with isUnsafe := true }] },
  places := solution.places.push (placeOf `App.Tree "App/CoreCode.lean" 30 "Tree") }

#guard rejects unsafeType (· matches .violation (.impure `App.Tree .coreCode [.«unsafe»]))
#guard !(errorsOf unsafeType).any (· matches .violation (.impure `App.Tree.casesOn ..))

def impureErrors (facts : Facts) : Array Lint.Error :=
  (errorsOf facts).filter (· matches .violation (.impure ..))

def mergedType : Facts := withSolution fun solution => { solution with
  inventory := { solution.inventory with declarations := solution.inventory.declarations ++
    #[{ declaration `App.Tree `App.CoreCode 30 true with isUnsafe := true },
      { declaration `App.Tree.casesOn `App.CoreCode 0 true with isUnsafe := true, effects := true }] },
  places := solution.places.push (placeOf `App.Tree "App/CoreCode.lean" 30 "Tree") }

#guard impureErrors mergedType == #[.violation (.impure `App.Tree .coreCode [.«unsafe», .io])]

def effectBox : Facts := withSolution fun solution => { solution with
  inventory := { solution.inventory with declarations := solution.inventory.declarations ++
    #[declaration `App.EffectBox `App.CoreCode 30 false, declaration `App.EffectBox.mk `App.CoreCode 30 false,
      { declaration `App.EffectBox.casesOn `App.CoreCode 0 true with effects := true },
      { declaration `App.EffectBox.recOn `App.CoreCode 0 true with effects := true }] },
  places := solution.places ++ #[placeOf `App.EffectBox "App/CoreCode.lean" 30 "EffectBox",
    placeOf `App.EffectBox.mk "App/CoreCode.lean" 30 "EffectBox"] }

#guard impureErrors effectBox == #[.violation (.impure `App.EffectBox .coreCode [.io])]
#guard contains (rendered effectBox) "App/CoreCode.lean:30: App.EffectBox uses IO in App.CoreCode (CoreCode)"
#guard contains (rendered effectBox) "Move App.EffectBox to a WorldCode module"
#guard !contains (rendered effectBox) "casesOn" && !contains (rendered effectBox) "recOn"

def placedConstructor : Facts := withSolution fun solution => { solution with
  inventory := { solution.inventory with declarations := solution.inventory.declarations ++
    #[declaration `App.Loop `App.CoreCode 30 false,
      { declaration `App.Loop.mk `App.CoreCode 31 true with isUnsafe := true }] },
  places := solution.places ++ #[placeOf `App.Loop "App/CoreCode.lean" 30 "Loop",
    placeOf `App.Loop.mk "App/CoreCode.lean" 31 "mk"] }

def parentedConstructor : Facts :=
  { placedConstructor with solution := { placedConstructor.solution with parents := #[(`App.Loop.mk, `App.Loop)] } }

#guard impureErrors placedConstructor == #[.violation (.impure `App.Loop.mk .coreCode [.«unsafe»])]
#guard impureErrors parentedConstructor == #[.violation (.impure `App.Loop .coreCode [.«unsafe»])]
#guard contains (rendered parentedConstructor) "App/CoreCode.lean:30: App.Loop uses `unsafe` in App.CoreCode (CoreCode)"
#guard Lint.settled #[(`App.Loop.mk.inner, `App.Loop.mk), (`App.Loop.mk, `App.Loop)] `App.Loop.mk.inner == `App.Loop

def hygienic : Name := Lean.addMacroScope `App.CoreCode `App.initFn 12

def initialized : Facts := withSolution fun solution => { solution with
  inventory := { solution.inventory with declarations := solution.inventory.declarations ++
    #[{ declaration `App.counter `App.CoreCode 40 true with initializes := true },
      { declaration hygienic `App.CoreCode 40 true with effects := true }] },
  places := solution.places ++ #[{ placeOf `App.counter "App/CoreCode.lean" 40 "counter" with
      firstLine := "initialize counter : IO.Ref Nat ← IO.mkRef 0" },
    placeOf hygienic "App/CoreCode.lean" 40 "initialize"] }

#guard impureErrors initialized == #[.violation (.impure `App.counter .coreCode [.initializer])]
#guard contains (rendered initialized) "`initialize counter : IO.Ref Nat ← IO.mkRef 0` runs IO when the program starts"

def generatedTwice : Facts := withSolution fun solution => { solution with
  inventory := { solution.inventory with declarations := solution.inventory.declarations ++
    #[declaration `App.Box `App.Solution 3 false, declaration `App.Box.casesOn `App.Solution 0 false,
      declaration `App.Box `App.CoreCode 30 false, declaration `App.Box.casesOn `App.CoreCode 0 false] },
  places := solution.places ++ #[placeOf `App.Box "App/Solution.lean" 3 "Box",
    placeOf `App.Box "App/CoreCode.lean" 30 "Box"] }

#guard (errorsOf generatedTwice).filter (· matches .declaredTwice ..) ==
  #[.declaredTwice `App.Box `App.Solution `App.CoreCode]

def sorryInLemmaLogged : Facts := withSolution fun solution => { solution with
  inventory := { solution.inventory with declarations := solution.inventory.declarations.map fun fact =>
    if fact.name == `App.fold_lemma then { fact with axioms := #[``sorryAx] } else fact },
  blames := #[blame `App.fold_lemma `App.fold_lemma `App.Solution],
  sorries := #[⟨"App/Solution.lean", 6⟩] }

#guard errorsOf sorryInLemmaLogged == #[.axiomUse (blame `App.fold_lemma `App.fold_lemma `App.Solution)]

def sorryElsewhere : Facts := { sorryInLemmaLogged with
  solution := { sorryInLemmaLogged.solution with sorries := #[⟨"App/Solution.lean", 6⟩, ⟨"App/Solution.lean", 30⟩] } }

#guard errorsOf sorryElsewhere ==
  #[.axiomUse (blame `App.fold_lemma `App.fold_lemma `App.Solution), .sorryUsed ⟨"App/Solution.lean", 30⟩]

def sorryOnly : Facts := withSolution ({ · with sorries := #[⟨"App/Solution.lean", 6⟩] })

#guard errorsOf sorryOnly == #[.sorryUsed ⟨"App/Solution.lean", 6⟩]

def foundIn (module : Name) (name : Name) (change : FoundFact → FoundFact := id) : Facts :=
  withSolution fun solution => { solution with
    found := solution.found.map fun found => if found.constant.name == name then change { found with module } else found }

def holeInSolution : Facts := foundIn `App.Solution `App.fold

#guard rejects holeInSolution (· matches .holeOutsideCode `App.fold `App.Solution)

def noncomputableHole : Facts := foundIn `App.CoreCode `App.fold ({ · with compiled := false })

#guard rejects noncomputableHole (· matches .holeNoncomputable `App.fold `App.CoreCode)

def fixpointHole : Facts := withSolution fun solution => { solution with fixpoints := #[`App.fold] }

#guard rejects fixpointHole (· matches .fixpointWithoutTerminates `App.fold `App.CoreCode)

def terminating : Facts := withChallenge fun challenge => { challenge with
  terminating := #[{ definition := `App.fold, headline := `App.fold_correct, place := ⟨"Challenge.lean", 8⟩ }] }

#guard rejects terminating (· matches .notFixpoint `App.fold `App.fold_correct)

def terminatingFixpoint : Facts := { terminating with solution := { solution with fixpoints := #[`App.fold] } }

#guard (errorsOf terminatingFixpoint).isEmpty

def twice : Facts := withSolution fun solution => { solution with inventory := { solution.inventory with
  declarations := solution.inventory.declarations.push (declaration `App.fold_lemma `App.CoreCode 9 false) } }

#guard rejects twice (· matches .declaredTwice `App.fold_lemma `App.Solution `App.CoreCode)

def mainInCode : Facts := withSolution fun solution => { solution with main? := some (`App.CoreCode, ⟨"App/CoreCode.lean", 9⟩) }

#guard rejects mainInCode (· matches .mainOutsideProgram `App.CoreCode)

def claimInCode : Facts := withSolution fun solution => { solution with
  registrations := #[{ registration with module := `App.CoreCode, home? := some `App.CoreCode }] }

#guard rejects claimInCode (· matches .claimOutsideWorldSpec `App.AddAgrees `App.CoreCode)

def rawClaim : Facts := withSolution fun solution => { solution with
  registrations := #[{ registration with module := `App.CoreCode }] }

#guard rejects rawClaim (· matches .unregisteredClaim { module := `App.CoreCode, .. })

def warning : LintFact :=
  { module := `App.CoreCode, place := ⟨"App/CoreCode.lean", 7⟩, linter := `linter.unusedVariables,
    message := "unused variable `x`\nnote: this linter can be disabled" }

def warned : Facts := withSolution ({ · with lints := #[warning] })

#guard rejects warned (· matches .lintWarning { linter := `linter.unusedVariables, .. })

def unreadSpec : Facts := withFiles fun files => { files with digests := files.digests.filter (·.path != "App/CoreSpec.lean") }

#guard rejects unreadSpec (· matches .ownedUnread "App/CoreSpec.lean")
#guard rejects unreadSpec (· matches .lock (.missing "App/CoreSpec.lean") (some (.specModule `App.CoreSpec)))

def edited : Facts := withFiles fun files => { files with
  digests := files.digests.map fun entry => if entry.path == "App/CoreSpec.lean" then { entry with digest := "9" } else entry }

#guard rejects edited (· matches .lock (.differs "App/CoreSpec.lean") (some (.specModule `App.CoreSpec)))
#guard (pendingOf { edited with solution := { solution with found := #[] } }).isEmpty

def lockless : Facts := withFiles ({ · with lock := .missing })

#guard rejects lockless (· matches .lockMissing)

def oldLock : Facts := withFiles ({ · with lock := .unreadable "it is not the JSON object `lake build` writes" })

#guard rejects oldLock (· matches .lockUnreadable _)

def noComparator : Facts := withFiles ({ · with comparator := .missing })

#guard rejects noComparator (· matches .comparatorMissing)

def garbledComparator : Facts := withFiles ({ · with comparator := .unreadable "expected a JSON object" })

#guard rejects garbledComparator (· matches .comparatorUnreadable _)

def staleComparator : Facts := withFiles ({ · with comparator := .decoded { config with
  theorems := #[`App.fold_correct, `App.old], solution := `B.Solution } })

#guard rejects staleComparator fun
  | .comparatorStale gone added listed expected =>
    gone == #[`App.old] && added == #[`App.fold_correct_rejects] && listed == some `B.Solution &&
      expected == some `App.Solution
  | _ => false

def staleAxioms : Facts := withFiles ({ · with comparator := .decoded { config with axioms := #[``propext] } })

#guard rejects staleAxioms (· matches .comparatorStale ..)

def targetless : Facts := withLake fun lake => { lake with defaultTargets := #[`App] }

#guard rejects targetless (· matches .noStatementTarget)

def targetlessLockless : Facts := { targetless with files := { files with lock := .missing, comparator := .missing } }

#guard (errorsOf targetlessLockless).any (· matches .noStatementTarget)
#guard !(errorsOf targetlessLockless).any (· matches .lockMissing)
#guard !(errorsOf targetlessLockless).any (· matches .comparatorMissing)

def noSolution : Facts := withLake fun lake => { lake with modules := lake.modules.filter (·.module != `App.Solution) }

#guard rejects noSolution (· matches .solutionModule #[])

def twoSolutions : Facts := withLake fun lake => { lake with
  modules := lake.modules.push (source `Other.Solution "Other/Solution.lean") }

#guard rejects twoSolutions (· matches .solutionModule #[`App.Solution, `Other.Solution])

def challengeLine : ImportLine := { module := `App.Solution, fact := runtime `Challenge 5, text := "import Challenge" }

def importsTheChallenge : Facts := withSolution fun solution => { solution with
  imports := solution.imports.push challengeLine }

#guard rejects importsTheChallenge (· matches .importsChallenge { module := `App.Solution, .. })

def builtinLinted : Facts := withLake ({ · with builtinLint := some ⟨"lakefile.lean", 5⟩ })

#guard rejects builtinLinted (· matches .builtinLintOn ⟨"lakefile.lean", 5⟩)

def unreadableProof : Facts :=
  foundIn `App.Solution `App.fold_correct fun found => { found with constant := { found.constant with value? := none } }

#guard rejects unreadableProof (· matches .proofUnreadable `App.fold_correct `App.Solution)

def missing (name : Name) : Facts := withSolution fun solution => { solution with
  found := solution.found.filter (·.constant.name != name) }

#guard pends (missing `App.fold_correct) (· matches .standing `App.fold_correct .absent)
#guard pends (missing `App.fold_correct_rejects) (· matches .standing `App.fold_correct_rejects .absent)

def unimplemented : Facts := { missing `App.fold with
  solution := { (missing `App.fold).solution with
    inventory := { solution.inventory with
      declarations := solution.inventory.declarations.filter (·.name != `App.fold) } } }

#guard pends unimplemented (· matches .standing `App.fold .absent)
#guard !(pendingOf unimplemented).any (· matches .unreachedHole _)

def outside : Facts := withSolution fun solution => { solution with
  found := solution.found.map fun found => if found.constant.name == `App.fold_correct then { found with module := `App.Proofs } else found,
  importsSolution := #[`App.Proofs] }

#guard pends outside (· matches .standing `App.fold_correct (.outside `App.Proofs true))

def restatedAs (change : ConstantFact → ConstantFact) : Facts :=
  foundIn `App.Solution `App.fold_correct fun found => { found with constant := change found.constant }

#guard pends (restatedAs ({ · with kind := .defined .safe })) (· matches .standing _ (.kind _ (.defined .safe)))
#guard pends (restatedAs ({ · with levels := [`u] })) (· matches .standing _ (.universes _ [`u]))
#guard pends (restatedAs ({ · with type := .sort .zero })) (· matches .standing _ (.differs ..))

def auxiliary : ConstantFact := constant `App.fold_correct.aux .proved (.sort .zero)

def withAuxiliary : Facts := withChallenge fun challenge => { challenge with
  headlines := challenge.headlines.map fun headline =>
    { headline with target := { headline.target with auxiliaries := #[auxiliary] } } }

#guard pends withAuxiliary (· matches .standing _ (.auxiliary `App.Solution `App.fold_correct.aux))

def auxiliaryFound : Facts := { withAuxiliary with
  solution := { solution with found := solution.found.push (found { foldCorrect with constant := auxiliary }
    `App.Solution "App/Solution.lean" 3) } }

#guard (Lint.run auxiliaryFound).code == 0

def mainless : Facts := withSolution ({ · with main? := none })

#guard pends mainless (· matches .mainMissing)

def library : Facts := { mainless with lake := { lake with defaultExeRoots := #[] } }

#guard (Lint.run library).code == 0

def unreached : Facts := withSolution ({ · with calls := #[(`main, #[`App.run])] })

#guard pends unreached (· matches .unreachedHole `App.fold)

def mainCallsItself : Facts := withSolution ({ · with calls := #[(`main, #[`main]), (`App.run, #[`App.fold])] })

#guard pends mainCallsItself (· matches .unreachedHole `App.fold)

def undecided : Facts := withSolution fun solution => { solution with
  claimUses := #[{ use with checks := #[(check, .undecided), (check, .matched)] }] }

#guard pends undecided (· matches .undecidedCheck ..)

def unchecked : Facts := withSolution fun solution => { solution with
  claimUses := #[{ use with checks := #[(check, .differs)] }] }

#guard pends unchecked (· matches .uncheckedClaim { checks := #[(_, .differs)], .. })

def unused : Facts := withSolution ({ · with claimUses := #[] })

#guard pends unused fun
  | .uncheckedClaim found => found.headline == `App.fold_correct && found.binder == 1 && found.checks.isEmpty
  | _ => false

def hidden : Facts := withLake fun lake => { lake with packages := #[{ dependency with
  configured := "/tmp/software_challenge", real := "/tmp/software_challenge" }] }

#guard pends hidden (· matches .hiddenDependency { name := `software_challenge, .. })

def insideRepository : Facts := withLake fun lake => { lake with packageDir := "/tmp/work", packages := #[{ dependency with
  configured := "/tmp/work/lsc", real := "/tmp/work/lsc" }] }

#guard (Lint.run insideRepository).code == 0

#guard (pendingOf { unreached with files := { files with lock := .decoded #[] } }).isEmpty
#guard (Lint.run { unreached with files := { files with lock := .decoded #[] } }).code == 1

end


meta def twoPrograms : Facts :=
  { complete with
    lake := { lake with defaultExeRoots := #[`App.WorldCode, `App.Tool] }
    solution := { solution with inventory := { solution.inventory with
      declarations := solution.inventory.declarations.push
        { declaration `main `App.Tool 3 true with effects := true } } } }

#guard !(errorsOf twoPrograms).any (· matches .declaredTwice ..)

meta def generatedEquations : Facts :=
  { complete with
    solution := { solution with inventory := { solution.inventory with
      declarations := solution.inventory.declarations ++
        #[{ declaration `App.fold.eq_1 `App.Solution 0 false with written := false },
          { declaration `App.fold.eq_1 `App.CoreCode 0 false with written := false }] } } }

#guard !(errorsOf generatedEquations).any (· matches .declaredTwice ..)

end SoftwareChallengeTests.Rules.Lint

module

meta import SoftwareChallengeTests.Rules.LintFacts

namespace SoftwareChallengeTests.Rules.LintMessages

open Lean SoftwareChallenge SoftwareChallengeTests.Rules.LintFacts

meta section

def errorTag : Lint.Error → Nat
  | .unaudited _ => 0
  | .unlinted _ => 1
  | .metaImportsEditable _ _ => 2
  | .violation _ => 3
  | .axiomUse _ => 4
  | .holeOutsideCode _ _ => 5
  | .holeNoncomputable _ _ => 6
  | .fixpointWithoutTerminates _ _ => 7
  | .declaredTwice _ _ _ => 8
  | .sorryUsed _ => 9
  | .mainOutsideProgram _ => 10
  | .notFixpoint _ _ => 11
  | .claimOutsideWorldSpec _ _ => 12
  | .unregisteredClaim _ => 13
  | .lintWarning _ => 14
  | .ownedUnread _ => 15
  | .lock _ _ => 16
  | .lockMissing => 17
  | .lockUnreadable _ => 18
  | .comparatorMissing => 19
  | .comparatorStale _ _ _ _ => 20
  | .comparatorUnreadable _ => 21
  | .noStatementTarget => 22
  | .solutionModule _ => 23
  | .importsChallenge _ => 24
  | .builtinLintOn _ => 25
  | .proofUnreadable _ _ => 26

def violationTag : Violation → Nat
  | .unplaced _ => 0
  | .legacy _ => 1
  | .forbiddenImport _ _ _ => 2
  | .axioms _ _ => 3
  | .impure _ _ _ => 4

def pendingTag : Lint.Pending → Nat
  | .standing _ _ => 0
  | .mainMissing => 1
  | .unreachedHole _ => 2
  | .undecidedCheck _ _ => 3
  | .uncheckedClaim _ => 4
  | .hiddenDependency _ => 5

def standingTag : Standing → Nat
  | .holds _ => 0
  | .unsound _ => 1
  | .absent => 2
  | .outside _ _ => 3
  | .kind _ _ => 4
  | .universes _ _ => 5
  | .differs _ _ _ => 6
  | .auxiliary _ _ => 7

def blame : AxiomBlame :=
  { declaration := `App.fold_correct, axiomName := ``sorryAx, culprit := `App.fold_lemma,
    culpritModule? := some `App.Solution }

def warning : LintFact :=
  { module := `App.CoreCode, place := ⟨"App/CoreCode.lean", 7⟩, linter := `linter.unusedVariables,
    message := "unused variable `x`\nnote: this linter can be disabled" }

def challengeLine : ImportLine := { module := `App.Solution, fact := runtime `Challenge 5, text := "import Challenge" }

def hiddenDependency : PackageFact :=
  { dependency with configured := "/tmp/software_challenge", real := "/tmp/software_challenge" }

def ownAxiom : AxiomBlame :=
  { blame with declaration := `App.fold_lemma, axiomName := `App.fold_lemma, culprit := `App.fold_lemma }

def violationSamples : Array Violation :=
  #[.unplaced `App.Stray, .legacy `App.CoreCode, .forbiddenImport `App.CoreCode `App.WorldCode .coreCode,
    .axioms `App.fold_lemma #[``sorryAx], .impure `App.fold .coreCode [.«unsafe»]]

def errorSamples : Array Lint.Error :=
  #[.unaudited `App.Tool, .unlinted `App.CoreCode,
    .metaImportsEditable `App.CoreSpec { name := `App.CoreCode, comptime := true, line := 4 }] ++
  violationSamples.map .violation ++
  #[.axiomUse blame, .holeOutsideCode `App.fold `App.Solution, .holeNoncomputable `App.fold `App.CoreCode,
    .fixpointWithoutTerminates `App.fold `App.CoreCode,
    .declaredTwice `App.fold_lemma `App.Solution `App.CoreCode, .sorryUsed ⟨"App/Solution.lean", 6⟩,
    .mainOutsideProgram `App.CoreCode, .notFixpoint `App.fold `App.fold_correct,
    .claimOutsideWorldSpec `App.AddAgrees `App.CoreCode, .unregisteredClaim { registration with module := `App.CoreCode },
    .lintWarning warning,
    .ownedUnread "App/CoreSpec.lean", .lock (.differs "App/CoreSpec.lean") (some (.specModule `App.CoreSpec)),
    .lock (.unrecorded "lean-toolchain") (some .toolchain), .lock (.unrecorded "App/CoreSpec/New.lean") none,
    .lock (.missing "App/WorldSpec.lean") (some (.specModule `App.WorldSpec)), .lockMissing,
    .lockUnreadable "it is not the JSON object `lake build` writes", .comparatorMissing,
    .comparatorStale #[`App.old] #[`App.fold_correct_rejects] (some `B.Solution) (some `App.Solution),
    .comparatorUnreadable "expected a JSON object", .noStatementTarget, .solutionModule #[],
    .solutionModule #[`App.Solution, `Other.Solution],
    .importsChallenge challengeLine,
    .builtinLintOn ⟨"lakefile.lean", 5⟩, .proofUnreadable `App.fold_correct `App.Solution]

def standingSamples : Array Standing :=
  #[.holds `App.Solution, .unsound `App.Solution, .absent, .outside `App.Proofs false, .outside `App.Proofs true,
    .kind `App.Solution (.defined .safe), .universes `App.Solution [`u],
    .differs `App.Solution "∀ (e : Expr), fold e = e" "∀ (e : App.Expr), @Eq App.Expr (App.fold e) e",
    .auxiliary `App.Solution `App.fold_correct.aux]

def pendingSamples : Array Lint.Pending :=
  standingSamples.map (.standing `App.fold_correct) ++ standingSamples.map (.standing `App.fold) ++
  #[.standing `App.fold_correct_rejects .absent, .mainMissing, .unreachedHole `App.fold,
    .undecidedCheck { use with checks := #[(check, .undecided)] } check, .uncheckedClaim { use with checks := #[] },
    .hiddenDependency hiddenDependency]

def follows (message : Message) : Bool :=
  let text := (Report.item message).toLower
  !message.place.file.isEmpty && message.place.line ≥ 1 && !message.what.isEmpty && !message.why.isEmpty &&
    !message.fix.isEmpty && !contains text " ask " && !contains text "owner"

#guard (List.range 27).all fun tag => errorSamples.any (errorTag · == tag)
#guard (List.range 5).all fun tag => violationSamples.any (violationTag · == tag)
#guard (List.range 6).all fun tag => pendingSamples.any (pendingTag · == tag)
#guard (List.range 8).all fun tag => standingSamples.any (standingTag · == tag)
#guard errorSamples.all fun error => follows (error.message complete)
#guard pendingSamples.all fun found => follows (found.message complete)

def says (message : Message) (fragments : List String) : Bool :=
  fragments.all (contains (Report.item message) ·)

def errorSays (facts : Facts) (error : Lint.Error) (fragments : List String) : Bool :=
  says (error.message facts) fragments

def pendingSays (facts : Facts) (found : Lint.Pending) (fragments : List String) : Bool :=
  says (found.message facts) fragments

#guard errorSays (withLake fun lake => { lake with exeRoots := lake.exeRoots.push `App.Tool }) (.unaudited `App.Tool)
  ["lakefile.lean:1: App.Tool is the root of the package's lean_exe, but no default target builds it",
    "mark that lean_exe `@[default_target]`", "delete owned.lock and run `lake build`, then run `lake lint`."]
#guard errorSays complete (.unaudited `App.CoreCode) ["App/CoreCode.lean:1:", "`lake build App.CoreCode`"]
#guard errorSays complete (.metaImportsEditable `App.CoreSpec { name := `App.CoreCode, comptime := true, line := 4 })
  ["App/CoreSpec.lean:4: App.CoreSpec (CoreSpec) meta-imports App.CoreCode (CoreCode)",
    "delete line 4, `meta import App.CoreCode`, from App/CoreSpec.lean; then delete owned.lock and run `lake build`"]
#guard errorSays complete (.violation (.unplaced `App.Stray))
  ["App/Stray.lean:1: no lean_lib of the package builds App.Stray", "so delete owned.lock and run `lake build`"]
#guard errorSays complete (.violation (.legacy `App.CoreCode))
  ["App/CoreCode.lean:1: App.CoreCode does not start with `module`", "Add `module` as the first line of App/CoreCode.lean"]
#guard errorSays complete (.violation (.forbiddenImport `App.CoreCode `App.WorldCode .coreCode))
  ["App/CoreCode.lean:1: App.CoreCode (CoreCode) imports App.WorldCode (WorldCode), but CoreCode may import only \
    CoreSpec and CoreCode modules and modules outside the package, so that pure code never reaches foreign code or \
    effects", "Delete line 1, `import App.WorldCode`, from App/CoreCode.lean, then run `lake lint`."]
#guard errorSays (withSolution fun solution => { solution with inventory := { solution.inventory with
    modules := solution.inventory.modules.map fun fact => if fact.name == `App.CoreCode then
      { fact with imports := #[runtime `App.WorldCode 4] } else fact } })
  (.violation (.forbiddenImport `App.CoreCode `App.WorldCode .coreCode)) ["App/CoreCode.lean:4:", "Delete line 4"]
#guard errorSays (withLake fun lake => { lake with modules := lake.modules.push (source `App.Tools "App/Tools.lean") })
  (.violation (.forbiddenImport `App.CoreCode `App.Tools .coreCode))
  ["Rename App.Tools to a CoreCode module, as in App.CoreCode.Tools (App/CoreCode/Tools.lean)"]
#guard errorSays complete (.violation (.forbiddenImport `App.CoreSpec `App.CoreCode .coreSpec))
  ["from App/CoreSpec.lean, which is owned, so then delete owned.lock and run `lake build`"]
#guard errorSays complete (.violation (.axioms `App.fold_lemma #[``sorryAx]))
  ["App/Solution.lean:6: App.fold_lemma uses `sorry`, so it is not proved",
    "Replace each `sorry` in App.fold_lemma with a proof or a definition, then run `lake lint`."]
#guard errorSays complete (.violation (.axioms `App.fold_lemma #[`App.fold_lemma._native.native_decide.ax_1_1]))
  ["is proved with `native_decide`, which asserts the evaluated result as an axiom", "with `decide`"]
#guard errorSays complete (.violation (.axioms `App.fold_lemma #[`App.raw]))
  ["App.fold_lemma depends on axiom App.raw, but the comparator permits only propext, Classical.choice, and \
    Quot.sound", "Prove App.fold_lemma without App.raw"]
#guard errorSays complete (.violation (.impure `App.fold .coreCode [.«unsafe», .io]))
  ["App/CoreCode.lean:5: App.fold uses `unsafe` and IO in App.CoreCode (CoreCode), but CoreCode code must be pure \
    and total, so that the proofs are about the code that runs",
    "Remove `unsafe` from App.fold and move App.fold to a WorldCode module, then run `lake lint`."]
#guard errorSays complete (.violation (.impure `App.fold .coreCode [.initializer]))
  ["`def fold` runs IO when the program starts, in App.CoreCode (CoreCode)", "Move it to a WorldCode module"]
#guard errorSays complete (.violation (.impure `App.fold .worldSpec [.unfoldableExtern]))
  ["`@[extern]` with a body the kernel unfolds", "Declare App.fold as `@[extern \"…\"] opaque`, with no body"]
#guard errorSays complete (.axiomUse blame)
  ["App/Solution.lean:10: App.fold_correct is not proved, because it uses App.fold_lemma (App/Solution.lean:6), \
    whose proof uses `sorry`", "Replace each `sorry` in App.fold_lemma with a proof or a definition"]
#guard errorSays complete (.axiomUse { blame with culprit := `Lib.broken, culpritModule? := some `Lib })
  ["App.fold_correct uses Lib.broken, which Lib declares outside the package, whose proof uses `sorry`, so the \
    proof of App.fold_correct is not checked", "Prove App.fold_correct without Lib.broken"]
#guard errorSays complete (.axiomUse ownAxiom) ["`axiom App.fold_lemma` asserts App.fold_lemma without proof"]
#guard errorSays complete (.holeOutsideCode `App.fold `App.Solution)
  ["hole App.fold is defined in App.Solution (tooling), but a hole is code",
    "Move `def fold` from App/Solution.lean to App/CoreCode.lean, or to a WorldCode module if it does IO, inside \
      `namespace App`"]
#guard errorSays complete (.holeNoncomputable `App.fold `App.CoreCode)
  ["App/CoreCode.lean:5: hole App.fold is `noncomputable` in App.CoreCode",
    "Define App.fold without `noncomputable` in App/CoreCode.lean"]
#guard errorSays complete (.fixpointWithoutTerminates `App.fold `App.CoreCode)
  ["is defined with `partial_fixpoint` in App.CoreCode", "marked `@[terminates App.fold]`",
    "without `partial_fixpoint`, in App/CoreCode.lean"]
#guard errorSays complete (.notFixpoint `App.fold `App.fold_correct)
  ["hole App.fold is not defined with `partial_fixpoint`, but `@[terminates App.fold]` on App.fold_correct \
    (Challenge.lean:8)", "Define App.fold with `partial_fixpoint` after its body in App/CoreCode.lean"]
#guard errorSays complete (.declaredTwice `App.fold_lemma `App.Solution `App.CoreCode)
  ["App.fold_lemma is declared in both App.CoreCode and App.Solution (App/Solution.lean:6)",
    "Rename or delete App.fold_lemma in App/CoreCode.lean"]
#guard errorSays complete (.sorryUsed ⟨"App/Solution.lean", 6⟩)
  ["App/Solution.lean:6: Lean reports `declaration uses 'sorry'` here", "Replace each `sorry` at App/Solution.lean:6"]
#guard errorSays complete (.mainOutsideProgram `App.CoreCode)
  ["App/CoreCode.lean:1: main is defined in App.CoreCode (CoreCode), but main runs the program, which does IO, and only WorldCode may",
    "Move `def main` from App/CoreCode.lean to App/WorldCode.lean, outside any namespace"]
#guard errorSays (withLake ({ · with exeRoots := #[`App.Main] })) (.mainOutsideProgram `App.Main)
  ["main is defined in App.Main, outside the package, the root of the package's lean_exe",
    "set that lean_exe's `root` to a WorldCode module, such as App.WorldCode.Main"]
#guard errorSays (withSolution fun solution => { solution with
    places := solution.places.push (placeOf `App.AddAgrees "App/CoreCode.lean" 9 "AddAgrees") })
  (.claimOutsideWorldSpec `App.AddAgrees `App.CoreCode)
  ["App/CoreCode.lean:9: WorldClaim App.AddAgrees is declared in App.CoreCode (CoreCode)", "only a WorldSpec module states",
    "Remove the `WorldClaim AddAgrees` command and its doc comment from App/CoreCode.lean"]
#guard errorSays complete (.unregisteredClaim { registration with module := `App.CoreCode })
  ["App.CoreCode adds App.AddAgrees, declared at App/WorldSpec.lean:7, to the world claims without the \
    `WorldClaim` command", "calls `SoftwareChallenge.claimsExt.addEntry`"]
#guard errorSays complete (.lintWarning warning)
  ["App/CoreCode.lean:7: Lean's linter linter.unusedVariables reports \"unused variable `x`\"",
    "Change line 7 of App/CoreCode.lean as the warning says"]
#guard !contains (Report.item ((Lint.Error.lintWarning warning).message complete)) "note:"
#guard errorSays complete (.lock (.differs "App/CoreSpec.lean") (some (.specModule `App.CoreSpec)))
  ["App/CoreSpec.lean:1: App/CoreSpec.lean differs from owned.lock",
    "`git checkout $(git log -1 --format=%H -- owned.lock) -- App/CoreSpec.lean`",
    "edit App/CoreCode.lean, App/WorldCode.lean, App/Solution.lean instead"]
#guard errorSays complete (.lock (.unrecorded "lean-toolchain") (some .toolchain))
  ["lean-toolchain is owned, because it fixes the Lean version", "Delete owned.lock and run `lake build` to record it"]
#guard !errorSays complete (.lock (.unrecorded "lean-toolchain") (some .toolchain)) ["Remove or rename"]
#guard errorSays complete (.lock (.unrecorded "App/CoreSpec/New.lean") none) ["Remove or rename App/CoreSpec/New.lean"]
#guard errorSays complete (.lock (.missing "App/WorldSpec.lean") (some (.specModule `App.WorldSpec)))
  ["App/WorldSpec.lean is recorded in owned.lock but missing"]
#guard errorSays complete (.lock (.differs "App/Notation.lean") (some (.closureModule `App.Notation)))
  ["Challenge.lean imports App.Notation, so it is part of the statement"]
#guard errorSays complete .lockMissing ["owned.lock is missing", "`git checkout -- owned.lock`"]
#guard errorSays complete .comparatorMissing ["comparator.json is missing", "Run `lake build`, then run `lake lint`."]
#guard errorSays complete (.comparatorStale #[`App.old] #[`App.fold_correct_rejects] (some `B.Solution)
    (some `App.Solution))
  ["comparator.json does not match Challenge.lean", "it lists App.old, which Challenge.lean no longer declares",
    "it omits App.fold_correct_rejects, which Challenge.lean declares",
    "it names the solution module \"B.Solution\", but the package's is \"App.Solution\""]
#guard errorSays complete (.comparatorStale #[] #[] (some `App.Solution) (some `App.Solution))
  ["its contents differ from what `lake build` writes"]
#guard errorSays complete .noStatementTarget ["lakefile.lean:1: lakefile.lean has no `statement` target",
  "then run `lake lint`:\n\n" ++ Lint.statementTarget]
#guard errorSays complete (.solutionModule #[])
  ["the package builds no module named Solution", "Create App/Solution.lean", "then run `lake build`."]
#guard errorSays complete (.solutionModule #[`App.Solution, `Other.Solution])
  ["App.Solution, Other.Solution are all named Solution"]
#guard errorSays complete (.importsChallenge challengeLine)
  ["App/Solution.lean:5: App.Solution imports Challenge, whose holes share names with the solution's definitions",
    "Replace `import Challenge` at App/Solution.lean:5 with imports of the CoreSpec and WorldSpec modules \
      App.Solution uses, such as `public import App.CoreSpec`"]
#guard errorSays complete (.builtinLintOn ⟨"lakefile.lean", 5⟩)
  ["lakefile.lean:5: the package block sets `builtinLint := true`", "delete owned.lock and run `lake build`"]
#guard errorSays complete (.proofUnreadable `App.fold_correct `App.Solution)
  ["App/Solution.lean:10: the proof of App.fold_correct in App.Solution cannot be read"]

#guard pendingSays complete (.standing `App.fold_correct .absent)
  ["Challenge.lean:8: App.fold_correct is not proved yet, so the solution does not claim it yet",
    "Add `theorem fold_correct (e : Expr) (h : AddAgrees nativeAdd) : fold e = e := …`, with a proof, to \
      App/Solution.lean, inside `namespace App`, then run `lake lint`."]
#guard pendingSays complete (.standing `App.fold .absent)
  ["Challenge.lean:5: hole App.fold is not implemented yet, so no headline about it can be proved",
    "Add `def fold : Expr → Expr := …` to App/CoreCode.lean, or to a WorldCode module if it does IO"]
#guard pendingSays complete (.standing `App.fold_correct_rejects .absent)
  ["App.fold_correct_rejects is not proved yet, so nothing shows that App.fold_correct rejects a wrong implementation"]
#guard pendingSays complete (.standing `App.fold_correct (.outside `App.Proofs false))
  ["App.fold_correct is in App.Proofs, which App.Solution does not import",
    "Add `public import App.Proofs` to the imports of App/Solution.lean"]
#guard pendingSays complete (.standing `App.fold_correct (.outside `App.Proofs true))
  ["App.fold_correct is in App.Proofs, which imports App.Solution, so App.Solution cannot import it back",
    "Move `theorem fold_correct` from App/Proofs.lean into App/Solution.lean, inside `namespace App`"]
#guard pendingSays complete (.standing `App.fold_correct (.kind `App.Solution (.defined .safe)))
  ["App.fold_correct is a def in App.Solution, but Challenge.lean:8 states it as a theorem",
    "Declare it with `theorem` in App/Solution.lean"]
#guard pendingSays complete (.standing `App.fold (.kind `App.CoreCode .opaqueConstant))
  ["hole App.fold is an opaque constant, as `partial def` and `opaque` declare, in App.CoreCode",
    "Define it with `def`, without `partial`, `unsafe`, or `opaque`"]
#guard pendingSays complete (.standing `App.fold_correct (.universes `App.Solution [`u]))
  ["App.fold_correct has universe parameters u in App.Solution, but none in Challenge.lean:8"]
#guard pendingSays complete (.standing `App.fold_correct
    (.differs `App.Solution "∀ (e : Expr), fold e = e" "∀ (e : App.Expr), @Eq App.Expr (App.fold e) e"))
  ["App.fold_correct states `∀ (e : Expr), fold e = e` in App.Solution, but \
    `∀ (e : Expr), AddAgrees nativeAdd → fold e = e` in Challenge.lean:8",
    "Restate it as `theorem fold_correct (e : Expr) (h : AddAgrees nativeAdd) : fold e = e := …`"]
#guard pendingSays complete (.standing `App.fold_correct (.differs `App.Solution
    "∀ (e : Expr), AddAgrees nativeAdd → fold e = e" "∀ (e : App.Expr), @App.Explicit e"))
  ["states `∀ (e : App.Expr), @App.Explicit e` in App.Solution, but `∀ (e : Expr), AddAgrees nativeAdd → fold e = e`"]
#guard pendingSays complete (.standing `App.fold_correct (.auxiliary `App.Solution `App.fold_correct.aux))
  ["App.fold_correct elaborates to App.fold_correct.aux in App.Solution, which differs from the \
    App.fold_correct.aux that Challenge.lean:8 elaborates to", "Copy the statement of App.fold_correct"]
#guard pendingSays complete .mainMissing
  ["App/WorldCode.lean:1: main is not written yet, but the package declares a lean_exe",
    "Add `def main : IO Unit := …` at the end of App/WorldCode.lean, outside any namespace, calling App.fold"]
#guard pendingSays complete (.unreachedHole `App.fold)
  ["Challenge.lean:5: hole App.fold is never called from main", "Call App.fold from main (App/WorldCode.lean:20)"]
#guard pendingSays complete (.undecidedCheck use check)
  ["App/WorldCode.lean:12: this Check cannot be matched against AddAgrees nativeAdd, which App.fold_correct assumes, \
    within the audit's budget of 200000 heartbeats", "as `Check AddAgrees nativeAdd …`"]
#guard pendingSays complete (.uncheckedClaim use)
  ["Challenge.lean:8: App.fold_correct assumes the world claim AddAgrees nativeAdd, which no Check tests against \
    the real foreign code", "Add `Check AddAgrees nativeAdd := do …`, or `Check AddAgrees nativeAdd : <an instance it \
      implies>`, to App/WorldCode.lean, then run `lake lint`."]
#guard pendingSays (withChallenge fun challenge => { challenge with
    headlines := challenge.headlines.map fun headline => { headline with
      claims := #[(1, `App.AddAgrees, "∀ t ∈ trials, AddAgrees t")] } })
  (.uncheckedClaim { use with statement := "AddAgrees t" })
  ["assumes the world claim ∀ t ∈ trials, AddAgrees t", "`Check AddAgrees t := do …`",
    "with a value of your choice in place of each variable it quantifies"]
#guard pendingSays complete (.hiddenDependency hiddenDependency)
  ["lakefile.lean:1: the comparator's sandbox hides package software_challenge at /tmp/software_challenge",
    "require software_challenge from git", "run `lake update software_challenge`"]

end

end SoftwareChallengeTests.Rules.LintMessages

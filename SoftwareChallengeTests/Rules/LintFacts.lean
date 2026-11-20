module

public meta import SoftwareChallenge.CoreCode.Rules.Lint

namespace SoftwareChallengeTests.Rules.LintFacts

open Lean SoftwareChallenge

public section

meta section

def expr : Shape := .const `App.Expr []

def foldType : Shape := .forallE expr expr

def correctType : Shape :=
  .forallE expr (.forallE (.app (.const `App.AddAgrees []) (.const `App.nativeAdd []))
    (.app (.app (.app (.const ``Eq [.succ .zero]) expr) (.app (.const `App.fold []) (.bvar 1))) (.bvar 1)))

def rejectsType : Shape := .app (.const ``Not []) (.const `App.wrong [])

def constant (name : Name) (kind : ConstantKind) (type : Shape) : ConstantFact :=
  { name, kind, levels := [], type, value? := some (.const `App.body []), hints := "", mutualBlock := [name],
    isPrivate := false }

def target (name : Name) (kind : ConstantKind) (type : Shape) (line : Nat) (written signature rendered : String) :
    TargetFact :=
  { constant := constant name kind type, place := ⟨"Challenge.lean", line⟩, written, enclosingNamespace := `App,
    signature, rendered, renderedExplicit := rendered, auxiliaries := #[] }

def fold : TargetFact :=
  target `App.fold (.defined .safe) foldType 5 "fold" ": Expr → Expr" "Expr → Expr"

def foldCorrect : TargetFact :=
  target `App.fold_correct .proved correctType 8 "fold_correct" "(e : Expr) (h : AddAgrees nativeAdd) : fold e = e"
    "∀ (e : Expr), AddAgrees nativeAdd → fold e = e"

def foldCorrectRejects : TargetFact :=
  target `App.fold_correct_rejects .proved rejectsType 11 "fold_correct_rejects" ": ¬ wrong" "¬wrong"

def agreesType : Shape := .app (.const `App.AddAgrees []) (.const `App.nativeAdd [])

def binderOf (name : String) (type : Shape) (prop : Bool) (shown : String) (variables : Array String := #[])
    (conclusion : String := shown) : BinderFact :=
  { name, type, meaning := type, prop, shown, conclusion, variables }

def correctHeadline : HeadlineFact :=
  { target := foldCorrect
    telescope := [binderOf "e" expr false "Expr", binderOf "h" agreesType true "AddAgrees nativeAdd"]
    killTemplate? := none, witness? := none }

def challenge : ChallengeFacts :=
  { module := `Challenge, file := "Challenge.lean", runtimeImports := #[], metaImports := #[],
    closure := #[`App.CoreSpec, `App.WorldSpec], headlines := #[correctHeadline],
    kills := #[{ target := foldCorrectRejects, headline := `App.fold_correct }], witnesses := #[], holes := #[fold],
    filled := #[], axioms := #[], terminating := #[], replaceable := #[`App.fold], claims := #[`App.AddAgrees] }

def source (module : Name) (file : String) : SourceFact := { module, file }

def dependency : PackageFact :=
  { name := `software_challenge, configured := "/work/.lake/packages/software_challenge",
    real := "/work/.lake/packages/software_challenge" }

def lake : LakeFacts :=
  { packageDir := "/work", configFiles := #["lakefile.lean", "lake-manifest.json", "lean-toolchain"],
    modules := #[source `App.CoreSpec "App/CoreSpec.lean", source `App.WorldSpec "App/WorldSpec.lean",
      source `App.CoreCode "App/CoreCode.lean", source `App.WorldCode "App/WorldCode.lean",
      source `App.Solution "App/Solution.lean"],
    challengeCandidates := #[source `Challenge "Challenge.lean"], defaultExeRoots := #[`App.WorldCode],
    packages := #[dependency],
    defaultTargets := #[`App, `statement], testDriver := "software_challenge/test_challenge",
    testDriverArgs := #[], testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, ownTests := #[], inputs := #[] }

def runtime (name : Name) (line : Nat) : ImportFact := { name, comptime := false, line }

def moduleFact (name : Name) (file : String) (imports : Array ImportFact) : ModuleFact :=
  { name, file, usesModuleSystem := true, imports }

def modules : Array ModuleFact :=
  #[moduleFact `App.CoreSpec "App/CoreSpec.lean" #[runtime `Init 3],
    moduleFact `App.WorldSpec "App/WorldSpec.lean" #[runtime `App.CoreSpec 3],
    moduleFact `App.CoreCode "App/CoreCode.lean" #[runtime `App.CoreSpec 3],
    moduleFact `App.WorldCode "App/WorldCode.lean" #[runtime `App.CoreCode 3, runtime `App.WorldSpec 4],
    moduleFact `App.Solution "App/Solution.lean" #[runtime `App.CoreCode 3, runtime `App.WorldCode 4]]

def importLines : Array ImportLine :=
  modules.flatMap fun fact => fact.imports.map fun dependency =>
    { module := fact.name, fact := dependency, text := s!"public import {dependency.name}" }

def declaration (name module : Name) (line : Nat) (computational : Bool) : DeclarationFact :=
  { name, module, line, computational, isUnsafe := false, isPartial := false, external := false,
    unfoldable := true, replaced := false, initializes := false, effects := false, debug := false, axioms := #[] }

def declarations : Array DeclarationFact :=
  #[declaration `App.AddAgrees `App.WorldSpec 7 false, declaration `App.fold `App.CoreCode 5 true,
    { declaration `App.run `App.WorldCode 15 true with effects := true },
    { declaration `main `App.WorldCode 20 true with effects := true },
    declaration `App.fold_lemma `App.Solution 6 false, declaration `App.fold_correct `App.Solution 10 false,
    declaration `App.fold_correct_rejects `App.Solution 14 false]

def found (target : TargetFact) (module : Name) (file : String) (line : Nat) : FoundFact :=
  { constant := target.constant, module, place := ⟨file, line⟩, compiled := true, rendered := target.rendered,
    renderedExplicit := target.renderedExplicit }

def check : CheckFact :=
  { claim := `App.AddAgrees, statement := "AddAgrees nativeAdd", place := ⟨"App/WorldCode.lean", 12⟩ }

def use : ClaimUse :=
  { headline := `App.fold_correct, binder := 1, claim := `App.AddAgrees, statement := "AddAgrees nativeAdd",
    checks := #[(check, .matched)] }

def registration : RegistrationFact :=
  { claim := `App.AddAgrees, module := `App.WorldSpec, home? := some `App.WorldSpec,
    place := ⟨"App/WorldSpec.lean", 7⟩ }

def placeOf (name : Name) (file : String) (line : Nat) (written : String) : DeclarationPlace :=
  { name, place := ⟨file, line⟩, written, firstLine := s!"def {written}" }

def solution : SolutionFacts :=
  { solution? := some `App.Solution, inventory := { modules, declarations }, blames := #[], imports := importLines,
    calls := #[(`main, #[`App.run]), (`App.run, #[`App.fold])],
    proofUses := #[(`App.fold_correct, #[`App.fold_lemma]), (`App.fold_lemma, #[])], meanings := #[],
    found := #[found fold `App.CoreCode "App/CoreCode.lean" 5, found foldCorrect `App.Solution "App/Solution.lean" 10,
      found foldCorrectRejects `App.Solution "App/Solution.lean" 14],
    solutionClosure := modules.map (·.name), importsSolution := #[], premiseUses := #[(`App.fold_correct, #[1])],
    claimUses := #[use], checks := #[check],
    registrations := #[registration],
    lints := #[], linted := modules.map (·.name), sorries := #[], fixpoints := #[],
    main? := some (`App.WorldCode, ⟨"App/WorldCode.lean", 20⟩),
    places := #[placeOf `App.AddAgrees "App/WorldSpec.lean" 7 "AddAgrees", placeOf `App.fold "App/CoreCode.lean" 5 "fold",
      placeOf `App.run "App/WorldCode.lean" 15 "run", placeOf `main "App/WorldCode.lean" 20 "main",
      placeOf `App.fold_lemma "App/Solution.lean" 6 "fold_lemma",
      placeOf `App.fold_correct "App/Solution.lean" 10 "fold_correct",
      placeOf `App.fold_correct_rejects "App/Solution.lean" 14 "fold_correct_rejects"] }

def digests : Array Lock.Entry :=
  #[⟨"lakefile.lean", "1"⟩, ⟨"lake-manifest.json", "2"⟩, ⟨"lean-toolchain", "3"⟩, ⟨"Challenge.lean", "4"⟩,
    ⟨"App/CoreSpec.lean", "5"⟩, ⟨"App/WorldSpec.lean", "6"⟩]

def config : Config :=
  { challenge := `Challenge, solution := `App.Solution, theorems := #[`App.fold_correct, `App.fold_correct_rejects],
    definitions := #[`App.fold], axioms := standardAxioms }

def files : FileFacts := { lock := .decoded digests, comparator := .decoded config, digests }

def complete : Facts := { lake, files, challenge, solution }

def withLake (change : LakeFacts → LakeFacts) : Facts := { complete with lake := change lake }

def withSolution (change : SolutionFacts → SolutionFacts) : Facts := { complete with solution := change solution }

def withChallenge (change : ChallengeFacts → ChallengeFacts) : Facts := { complete with challenge := change challenge }

def withFiles (change : FileFacts → FileFacts) : Facts := { complete with files := change files }

def errorsOf (facts : Facts) : Array Lint.Error := (Lint.run facts).errors

def pendingOf (facts : Facts) : Array Lint.Pending := (Lint.run facts).pending

def rendered (facts : Facts) : String := "\n".intercalate (Lint.run facts).report.toList

def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

end

end

end SoftwareChallengeTests.Rules.LintFacts

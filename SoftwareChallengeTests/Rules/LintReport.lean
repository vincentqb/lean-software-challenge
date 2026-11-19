module

meta import SoftwareChallengeTests.Rules.LintFacts

namespace SoftwareChallengeTests.Rules.LintReport

open Lean SoftwareChallenge SoftwareChallengeTests.Rules.LintFacts

meta section

#guard (Lint.run complete).report ==
  #["fold_correct  assumes AddAgrees (1 check)", "Proved: 1 of 1 headlines, 1 of 1 kills",
    "Edit: App/CoreCode.lean App/WorldCode.lean App/Solution.lean",
    "Owned: lakefile.lean lake-manifest.json lean-toolchain owned.lock Challenge.lean App/CoreSpec.lean \
      App/WorldSpec.lean"]

def headlineLine (facts : Facts) : String := ((Report.headlineLines facts)[0]?.map (·.render)).getD ""

#guard headlineLine (withSolution ({ · with premiseUses := #[(`App.fold_correct, #[])] })) ==
  "fold_correct  assumes AddAgrees (1 check, unused by the proof)"

#guard headlineLine (withSolution ({ · with premiseUses := #[] })) == "fold_correct  assumes AddAgrees (1 check)"

#guard headlineLine (withSolution ({ · with claimUses := #[] })) == "fold_correct  assumes AddAgrees (0 checks)"

def twoChecks : Facts := withSolution ({ · with claimUses := #[{ use with checks := #[(check, .matched),
  (check, .matched), (check, .differs)] }] })

#guard headlineLine twoChecks == "fold_correct  assumes AddAgrees (2 checks)"

def without (name : Name) : Facts := withSolution fun solution =>
  { solution with found := solution.found.filter (·.constant.name != name), premiseUses := #[(name, #[])] }

#guard headlineLine (without `App.fold_correct) == "fold_correct  assumes AddAgrees (1 check)  (not yet proved)"
#guard headlineLine (without `App.fold_correct_rejects) == "fold_correct  assumes AddAgrees (1 check)  (kill not yet proved)"

def restated : Facts := withSolution fun solution => { solution with
  found := solution.found.map fun found => if found.constant.name == `App.fold_correct then
    { found with constant := { found.constant with type := .sort .zero } } else found }

#guard headlineLine restated == "fold_correct  assumes AddAgrees (1 check)  (stated differently)"

def outside : Facts := withSolution fun solution => { solution with
  found := solution.found.map fun found => if found.constant.name == `App.fold_correct then
    { found with module := `App.Proofs } else found }

#guard headlineLine outside == "fold_correct  assumes AddAgrees (1 check)  (outside Solution's imports)"

def sorried : Facts := withSolution fun solution => { solution with inventory := { solution.inventory with
  declarations := solution.inventory.declarations.map fun fact =>
    if fact.name == `App.fold_correct then { fact with axioms := #[``sorryAx] } else fact } }

#guard headlineLine sorried == "fold_correct  assumes AddAgrees (1 check)  (not yet proved)"
#guard (Report.provedLine sorried) == "Proved: 0 of 1 headlines, 1 of 1 kills"

def idempotentType : Shape :=
  .forallE expr (.app (.app (.app (.const ``Eq [.succ .zero]) expr)
    (.app (.const `App.fold []) (.app (.const `App.fold []) (.bvar 0)))) (.app (.const `App.fold []) (.bvar 0)))

def idempotent : TargetFact :=
  target `App.fold_idempotent .proved idempotentType 14 "fold_idempotent" "(e : Expr) : fold (fold e) = fold e"
    "∀ (e : Expr), fold (fold e) = fold e"

def idempotentHeadline : HeadlineFact :=
  { target := idempotent, binders := [⟨.input, false, []⟩], claims := #[], unnamed := #[], mentions := #[`App.fold],
    killTemplate? := none, witness? := none }

def replacement : Witnesses := [(`App.fold, .lam expr (.bvar 0))]

def independenceType : Shape :=
  Shape.conjunction ((correctType.subst challenge.isReplaceable replacement).negation ::
    [idempotentType.subst challenge.isReplaceable replacement])

def independence : TargetFact :=
  target `App.fold_correct_rejects_independently .proved independenceType 20 "fold_correct_rejects_independently"
    "" ""

def corollary : Facts :=
  let challenge := { challenge with
    headlines := challenge.headlines.push idempotentHeadline,
    kills := challenge.kills.push { target := independence, headline := `App.fold_correct } }
  { complete with
    challenge,
    solution := { solution with
      found := solution.found ++ #[found idempotent `App.Solution "App/Solution.lean" 20,
        found independence `App.Solution "App/Solution.lean" 30],
      proofUses := #[(`App.fold_correct, #[`App.fold_lemma]), (`App.fold_lemma, #[`App.fold_idempotent]),
        (`App.fold_idempotent, #[`App.fold_correct_rejects])] } }

#guard (Report.headlineLines corollary).map (·.render) ==
  #["fold_correct  assumes AddAgrees (1 check)  (follows from fold_idempotent)", "fold_idempotent"]
#guard Report.independentLine? corollary == some "Independent: 1 of 2 headlines"
#guard Report.independentLine? complete == none
#guard Lint.followsFrom (Lint.proofGraph corollary.solution) #[`App.fold_correct, `App.fold_idempotent] `App.fold_idempotent == #[]
#guard Lint.followsFrom (Lint.proofGraph corollary.solution) #[`App.fold_correct] `App.fold_idempotent == #[]
#guard Lint.followsFrom (Lint.proofGraph corollary.solution) #[`App.fold_idempotent] `App.fold_correct == #[`App.fold_idempotent]

def throughOther : SolutionFacts :=
  { solution with proofUses := #[(`H, #[`G]), (`G, #[`K]), (`K, #[])] }

#guard Lint.followsFrom (Lint.proofGraph throughOther) #[`H, `G, `K] `H == #[`G]
#guard Lint.followsFrom (Lint.proofGraph throughOther) #[`H, `K] `H == #[`K]

#guard (Report.headlineLines { corollary with solution := { corollary.solution with
  found := corollary.solution.found.filter (·.constant.name != `App.fold_idempotent) } }).map (·.render) ==
  #["fold_correct  assumes AddAgrees (1 check)", "fold_idempotent  (not yet proved)"]

#guard Lint.unreachedHoles solution #[`App.fold, `App.run, `App.fold_lemma] == #[`App.fold_lemma]
#guard Lint.unreachedHoles { solution with calls := #[(`main, #[`App.run])] } #[`App.fold] == #[`App.fold]
#guard (Lint.solutionClosure modules `App.Solution).size == 6
#guard (Lint.solutionClosure modules `App.Solution).contains `App.CoreSpec && (Lint.solutionClosure modules `App.Solution).contains `Init
#guard !(Lint.solutionClosure modules `App.CoreCode).contains `App.WorldCode
#guard Lint.importingSolution modules `App.CoreCode == #[`App.WorldCode, `App.Solution]
#guard Lint.importingSolution modules `App.Solution == #[]

def termination : TerminationFact :=
  { definition := `App.fold, headline := `App.fold_correct, place := ⟨"Challenge.lean", 8⟩ }

def terminating : Facts := { complete with
  challenge := { challenge with terminating := #[termination] },
  solution := { solution with fixpoints := #[`App.fold] } }

#guard Report.terminationLines terminating == #["fold terminates via fold_correct"]
#guard (Lint.run terminating).report.contains "fold terminates via fold_correct"

def failing : Facts := withSolution fun solution => { solution with
  sorries := #[⟨"App/Solution.lean", 6⟩, ⟨"App/Solution.lean", 6⟩],
  found := solution.found.filter (·.constant.name != `App.fold_correct_rejects) }

#guard contains (rendered failing) "Errors: 1\n  App/Solution.lean:6: Lean reports `declaration uses 'sorry'` here"
#guard contains (rendered failing) "Pending: 1\n  Challenge.lean:11: App.fold_correct_rejects is not proved yet"
#guard (Lint.run failing).code == 1
#guard contains (rendered failing) "lake lint found 1 error, as listed under Errors above"

def ordered : Facts := withSolution fun solution => { solution with found := #[] }

#guard (Lint.run ordered).code == 2
#guard contains (rendered ordered) "Pending: 3\n  Challenge.lean:5: hole App.fold is not implemented yet"
#guard contains (rendered ordered) "\n  Challenge.lean:8: App.fold_correct is not proved yet"
#guard contains (rendered ordered) "\n  Challenge.lean:11: App.fold_correct_rejects is not proved yet"
#guard !contains (rendered ordered) "never called from main"
#guard ((Lint.run ordered).report.back?) ==
  some "lake lint found no errors, but 3 items are pending, as listed under Pending above, so the solution is not \
    complete. Do each as it says, then run `lake lint`."

def wrong (next : Next) : Message :=
  { place := ⟨"A.lean", 3⟩, what := "x is wrong", why := "so y fails", fix := "Fix x", next }

#guard Report.item (wrong .test) == "A.lean:3: x is wrong, so y fails. Fix x, then run `lake test`."
#guard Report.item (wrong (.grade "abc")) == "A.lean:3: x is wrong, so y fails. Fix x, then run `lake exe grade abc`."
#guard Report.listing "Errors" #["a\nb"] == "Errors: 1\n  a\n    b"

end

end SoftwareChallengeTests.Rules.LintReport

module

meta import SoftwareChallengeReadTests.Support
meta import SoftwareChallenge.CoreCode.Rules.Lint

namespace SoftwareChallengeReadTests.Closure

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def readFixture (name : Name) : Name := `SoftwareChallengeReadTests.Fixtures ++ name

def importsHole : Name := readFixture `CoreSpec.ImportsHole

def metaTooling : Name := readFixture `WorldSpec.MetaTooling

def tactics : Name := readFixture `Tactics

def modules : Array Name :=
  #[fixture `CoreSpec, fixture `WorldSpec, fixture `Standing.Solution, tactics, importsHole, metaTooling]

def statementChallenge (lake : LakeFacts) : IO ChallengeFacts := do
  let some candidate := challengeOf? lake | throw <| .userError "the fixture lake facts name no challenge"
  let imported ← challengeEnv { lake with challengeCandidates := #[] } candidate.module .build
  let challenge ← challengeFacts lake candidate imported .build
  return { challenge with owned := ← readOwned lake challenge .build }

run_cmd Elab.Command.liftCoreM do
  let lake ← lakeOf modules (some (fixture `Standing.Challenge))
  let challenge ← statementChallenge lake
  check (challenge.closure.contains (fixture `WorldSpec) && ![importsHole, metaTooling, tactics,
      fixture `Standing.Solution].any challenge.closure.contains)
    s!"the challenge's closure holds modules that only a spec module outside it imports: {challenge.closure}"
  check (Statement.ownedRoots lake challenge == #[fixture `CoreSpec, fixture `WorldSpec, importsHole, metaTooling])
    s!"the owned modules the statement step reads were misread: {Statement.ownedRoots lake challenge}"
  check (!(Statement.ownedPaths lake challenge).any (·.endsWith "Tactics.lean") &&
      !(Statement.ownedPaths lake challenge).any (·.endsWith "Standing/Solution.lean"))
    s!"a module that only a spec module imports was owned: {Statement.ownedPaths lake challenge}"
  check ((Statement.ownedViolationErrors lake challenge).contains
      (.ownedViolation (.forbiddenImport importsHole (fixture `Standing.Solution) .coreSpec)))
    s!"a CoreSpec module that imports the hole's implementation was not refused: \
      {repr (Statement.ownedViolationErrors lake challenge)}"
  check ((Statement.specImportErrors lake challenge).contains
      (.specImport metaTooling { name := tactics, comptime := true, line := 3 }))
    s!"a WorldSpec module that meta-imports a tooling module was not refused: \
      {repr (Statement.specImportErrors lake challenge)}"
  let solution ← readSolution lake challenge .lint
  let facts : Facts := { lake, files := default, challenge, solution }
  check ((Lint.editableMetaImports facts).contains (.metaImportsEditable metaTooling
      { name := tactics, comptime := true, line := 3 }))
    s!"lint did not refuse a WorldSpec module that meta-imports a tooling module: \
      {repr (Lint.editableMetaImports facts)}"
  check (!(Lint.ownedPaths facts).any (·.endsWith "Tactics.lean"))
    s!"lint owned a module that only a spec module imports: {Lint.ownedPaths facts}"

run_cmd Elab.Command.liftCoreM do
  let unbuilt := readFixture `Unbuilt
  let lake := { (← lakeOf #[fixture `Program]) with exeRoots := #[fixture `Program, unbuilt] }
  let challenge := emptyChallenge .anonymous ""
  let solution ← readSolution lake challenge .lint
  let facts : Facts := { lake, files := default, challenge, solution }
  check (Lint.unauditedExeRoots facts == #[.unaudited unbuilt])
    s!"an executable root that no default target builds was not reported unaudited: \
      {repr (Lint.unauditedExeRoots facts)}"

end

end SoftwareChallengeReadTests.Closure

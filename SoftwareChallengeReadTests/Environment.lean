module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Environment

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def declaredIn (solution : SolutionFacts) (name : Name) : Array (Name × Nat) :=
  (solution.inventory.declarations.filter (·.name == name)).map fun fact => (fact.module, fact.line)

def placedIn (solution : SolutionFacts) (name : Name) : Array (String × Nat) :=
  (solution.places.filter (·.name == name)).map fun found => (found.place.file, found.place.line)

def unread : ChallengeFacts := emptyChallenge .anonymous ""

run_cmd Elab.Command.liftCoreM do
  let solution ← readSolution (← lakeOf #[fixture `Declared, fixture `Redeclared]) unread .lint
  for (name, line) in [(`shared, 7), (`shared_value, 9)] do
    check (declaredIn solution (fixture name) == #[(fixture `Declared, line), (fixture `Redeclared, line)] &&
        placedIn solution (fixture name) == #[("SoftwareChallengeTests/Fixtures/Declared.lean", line),
          ("SoftwareChallengeTests/Fixtures/Redeclared.lean", line)])
      s!"{name}, which two catalog modules declare, was not recorded in both: {declaredIn solution (fixture name)}"
  check ((solution.inventory.declarations.filter (·.name == fixture `shared_value)).map (·.axioms) == #[#[], #[]])
    "a theorem two modules declare with different statements was not read from each module's own constant"

run_cmd Elab.Command.liftCoreM do
  let refused ← refusal (discard (readSolution (← lakeOf #[fixture `Redeclared, fixture `SharedUser]) unread .lint))
  check (refused.any fun message => contains message
      "SoftwareChallengeTests/Fixtures/Redeclared.lean:7: SoftwareChallengeTests.Fixtures.shared is declared both in \
        SoftwareChallengeTests.Fixtures.Redeclared and in SoftwareChallengeTests.Fixtures.Declared" &&
      contains message "Rename SoftwareChallengeTests.Fixtures.shared in SoftwareChallengeTests/Fixtures/Redeclared.lean, \
        then run `lake lint`." && contains message "SoftwareChallengeTests.Fixtures.shared_value is declared both")
    s!"a name that a catalog module shares with a module outside the package was not refused with its fix: {refused}"

run_cmd Elab.Command.liftCoreM do
  let lake := { (← lakeOf #[fixture `Program, fixture `SecondProgram]) with
    exeRoots := #[fixture `Program, fixture `SecondProgram] }
  let solution ← readSolution lake unread .lint
  check (declaredIn solution `main == #[(fixture `Program, 7), (fixture `SecondProgram, 5)])
    s!"the two executables' main were not both recorded: {declaredIn solution `main}"
  check (solution.main?.map (·.1) == some (fixture `Program)) "main was not read from the first executable root"

run_cmd Elab.Command.liftCoreM do
  let modules := #[`CoreSpec, `WorldSpec, `Standing.Solution, `Standing.Outside, `Standing.Importer].map fixture
  let lake ← lakeOf modules (some (fixture `Standing.Challenge))
  let solution ← readSolution lake (← readChallenge lake .lint) .lint
  check (solution.imports.any fun line => line.module == fixture `Standing.Importer &&
      line.fact.name == fixture `Standing.Challenge && line.fact.line == 3)
    "the import of the challenge by a catalog module was not read"
  check ((solution.found.find? (·.constant.name == fixture `Standing.hole)).any (·.module == fixture `Standing.Solution))
    "the hole was not read from the catalog module that defines it"
  check (declaredIn solution (fixture `Standing.hole) == #[(fixture `Standing.Solution, 9)])
    s!"the challenge's hole was recorded among the catalog's declarations: {declaredIn solution (fixture `Standing.hole)}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `Linted
  let lake ← lakeOf #[module]
  let built := oleanOf lake module
  for missing in ["server", "private"] do
    let dir := (← IO.currentDir) / ".lake" / "build" / "readTests" / "parts"
    if ← dir.pathExists then IO.FS.removeDirAll dir
    let scratch := { lake with packageDir := dir.toString }
    let olean := oleanOf scratch module
    IO.FS.createDirAll (olean.parent.getD dir)
    for (part, copy) in [(built, olean), (built.addExtension "server", olean.addExtension "server"),
        (built.addExtension "private", olean.addExtension "private"), (built.withExtension "ir.sig",
          olean.withExtension "ir.sig"), (built.withExtension "ir", olean.withExtension "ir")] do
      unless part == built.addExtension missing do IO.FS.writeBinFile copy (← IO.FS.readBinFile part)
    let refused ← refusal (discard (readSolution scratch unread .lint))
    check (refused.any fun message => contains message "SoftwareChallengeTests/Fixtures/Linted.lean:1:" &&
        contains message s!"lacks {olean.addExtension missing}" &&
        contains message "Run `lake build SoftwareChallengeTests.Fixtures.Linted`" &&
        contains message "then run `lake lint`.")
      s!"a module compiled without its .olean.{missing} was not refused with its fix: {refused}"
    IO.FS.removeDirAll dir

end

end SoftwareChallengeReadTests.Environment

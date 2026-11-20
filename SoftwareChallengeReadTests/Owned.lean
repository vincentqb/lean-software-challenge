module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Owned

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def ownedModules : Array Name := #[`CoreSpec, `CoreSpec.Derived, `WorldSpec, `CoreCode, `CoreCode.Derived].map fixture

run_cmd Elab.Command.liftCoreM do
  let lake ← lakeOf ownedModules (some (fixture `Challenge))
  let read ← readChallenge lake .build
  let challenge := { read with owned := ← readOwned lake read .build }
  let owned := challenge.owned
  check (owned.inventory.modules.map (·.name) == #[`CoreSpec, `CoreSpec.Derived, `WorldSpec, `CoreCode].map fixture)
    s!"the statement step did not read every CoreSpec and WorldSpec module and the challenge's package imports: \
      {owned.inventory.modules.map (·.name)}"
  let derived := owned.inventory.declarations.filterMap fun fact =>
    if fact.derivedPartial then some (fact.name, fact.module) else none
  check (derived == #[(fixture `instBEqForest.beq, fixture `CoreSpec.Derived)])
    s!"the partial instances that deriving generates, and only those that do not recurse structurally, were \
      misread: {derived}"
  check (Statement.derivedPartialErrors challenge ==
      #[.derivedPartial (fixture `instBEqForest.beq) (fixture `CoreSpec.Derived)])
    "a partial instance that deriving generates in a CoreSpec module was not reported to the owner"
  check (owned.registrations.any fun registration => registration.claim == fixture `SuccAgrees &&
      registration.home? == some (fixture `WorldSpec) && registration.place.line > 0)
    "the WorldSpec module's claims were misread"
  let refusedClaims := (Statement.ownedClaimErrors lake challenge).filterMap fun error => match error with
    | .ownedClaim registration => some (registration.claim, registration.module)
    | _ => none
  check (refusedClaims == #[(fixture `CoreClaim, fixture `CoreCode)])
    s!"only the WorldClaim that the challenge's CoreCode import declares is the owner's to move: {refusedClaims}"
  check ((Statement.ownedViolationErrors lake challenge).all fun error => match error with
      | .ownedViolation (.impure name .coreSpec _) =>
        (privateToUserName name).toString.startsWith (toString (fixture `instBEqForest))
      | _ => false)
    s!"an owned module was refused for what it may do: {repr (Statement.ownedViolationErrors lake challenge)}"
  check (owned.parents.contains (fixture `Forest.grove, fixture `Forest) &&
      owned.parents.contains (fixture `Forest.rec, fixture `Forest) &&
      owned.parents.contains (fixture `Forest.casesOn, fixture `Forest))
    "the declarations Lean generates for an inductive were not given the inductive as parent"
  check (owned.places.any fun found => found.name == fixture `Forest && found.place.line == 7 &&
      found.place.file == "SoftwareChallengeTests/Fixtures/CoreSpec/Derived.lean") "an owned declaration was misplaced"
  check (owned.imports.any fun line => line.module == fixture `WorldSpec && line.fact.name == fixture `CoreSpec &&
      line.text == "public import SoftwareChallengeTests.Fixtures.CoreSpec") "an owned module's import line was misread"
  check (challenge.imports.any fun (module, imports) => module == fixture `CoreCode &&
      imports.contains (fixture `CoreSpec)) "the import edges of the challenge's closure were misread"
  check (Statement.ownedRoots lake challenge == #[`CoreSpec, `CoreSpec.Derived, `WorldSpec, `CoreCode].map fixture)
    s!"the owned modules the statement step reads were misread: {Statement.ownedRoots lake challenge}"

run_cmd Elab.Command.liftCoreM do
  let lake ← lakeOf #[] (some (fixture `KeptChallenge))
  let refused ← refusal (discard (readListedChallenge lake .build))
  check (refused.any fun message => contains message "SoftwareChallenge/Commands/Links.lean:1:" &&
      contains message "lake.json does not list it among the package's modules" &&
      contains message "no edit to the package fixes this" && contains message "then run `lake build`.")
    s!"a challenge closure module that lake.json omits was not refused: {refused}"
  let read ← readChallenge lake .build
  let listed ← read.closure.filterM fun module => (oleanOf lake module).pathExists
  let full ← lakeOf listed (some (fixture `KeptChallenge))
  check ((← refusal (discard (readListedChallenge full .build))).isNone)
    "a challenge whose closure lake.json lists in full was refused"

run_cmd Elab.Command.liftCoreM do
  let lake ← lakeOf #[fixture `CoreCode.Derived]
  let solution ← readSolution lake (emptyChallenge .anonymous "") .lint
  check (solution.parents.contains (fixture `Rose.node, fixture `Rose) &&
      solution.parents.contains (fixture `Rose.rec, fixture `Rose))
    s!"the solution's generated declarations were not given their parents: {solution.parents}"

end

end SoftwareChallengeReadTests.Owned

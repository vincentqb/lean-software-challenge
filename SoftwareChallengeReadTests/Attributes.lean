module

meta import SoftwareChallengeReadTests.Support
meta import SoftwareChallenge.CoreCode.Rules.Lint

namespace SoftwareChallengeReadTests.Attributes

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def lintFacts (module : Name) : IO Facts := do
  let lake ← lakeOf #[module]
  let challenge := emptyChallenge .anonymous ""
  return { lake, files := default, challenge, solution := ← readSolution lake challenge .lint }

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.Replaced
  let facts ← lintFacts module
  let replaced := (facts.solution.inventory.declarations.filter (·.countsAsReplaced)).map (·.name)
  check (replaced == #[module ++ `Coin.tails, module ++ `Coin.rec])
    s!"the constructor and the recursor that `attribute [implemented_by …]` replaces were not read as replaced: \
      {replaced}"
  check (Lint.violations facts == #[.violation (.impure (module ++ `Coin.tails) .coreCode [.implementedBy]),
      .violation (.impure (module ++ `Coin.rec) .coreCode [.implementedBy])])
    s!"a CoreCode constructor or recursor with @[implemented_by] was not refused: {repr (Lint.violations facts)}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreSpec.Replaced
  let lake ← lakeOf #[module]
  let unread := emptyChallenge .anonymous ""
  let challenge := { unread with owned := ← readOwned lake unread .build }
  let errors := Statement.ownedViolationErrors lake challenge
  check (errors == #[.ownedViolation (.impure (module ++ `Side.right) .coreSpec [.implementedBy])])
    s!"a CoreSpec constructor with @[implemented_by] was not reported to the owner: {repr errors}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.Extern
  let facts ← lintFacts module
  check (Lint.violations facts == #[.violation (.impure (module ++ `Coin.tails) .coreCode [.extern])])
    s!"a CoreCode constructor with @[extern] was not refused: {repr (Lint.violations facts)}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `WorldSpec.Extern
  let lake ← lakeOf #[module]
  let unread := emptyChallenge .anonymous ""
  let challenge := { unread with owned := ← readOwned lake unread .build }
  let errors := Statement.ownedViolationErrors lake challenge
  check (errors == #[.ownedViolation (.impure (module ++ `Coin.tails) .worldSpec [.extern]),
      .ownedViolation (.impure (module ++ `Width) .worldSpec [.extern])])
    s!"a WorldSpec constructor or type with @[extern] was not reported to the owner: {repr errors}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.Csimp
  let facts ← lintFacts module
  let proof := module ++ `keep_eq_bump
  check ((facts.solution.inventory.declarations.find? (·.name == proof)).any fun fact =>
      fact.isUnsafe && !fact.computational) "the unsafe proof that @[csimp] trusts was misread"
  check (Lint.violations facts == #[.violation (.impure proof .coreCode [.«unsafe»])])
    s!"an unsafe proof that @[csimp] trusts was not refused: {repr (Lint.violations facts)}"

end

end SoftwareChallengeReadTests.Attributes

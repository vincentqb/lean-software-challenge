module

meta import SoftwareChallengeReadTests.Support
meta import SoftwareChallenge.CoreCode.Rules.Lint
meta import SoftwareChallenge.CoreCode.Report.StatementMessages

namespace SoftwareChallengeReadTests.Purity

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def lintFacts (module : Name) : IO Facts := do
  let lake ← lakeOf #[module]
  let challenge := emptyChallenge .anonymous ""
  return { lake, files := default, challenge, solution := ← readSolution lake challenge .lint }

def refusals (facts : Facts) : Array Lint.Error :=
  Lint.groupImpure facts (Lint.violations facts)

def rendered (facts : Facts) : Array String :=
  (refusals facts).map fun error => Report.item (error.message facts)

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.Replaced
  let facts ← lintFacts module
  let replaced := (facts.solution.inventory.declarations.filter (·.replaced)).map (·.name)
  check (replaced == #[module ++ `Coin.tails])
    s!"only the constructor that `attribute [implemented_by …]` replaces was to be read as replaced: {replaced}"
  check (refusals facts == #[.violation (.impure (module ++ `Coin.tails) .coreCode [.implementedBy])])
    s!"a CoreCode constructor with @[implemented_by] was not refused: {repr (refusals facts)}"
  check (rendered facts == #[
      s!"SoftwareChallengeTests/Fixtures/CoreCode/Replaced.lean:9: {module}.Coin.tails uses `@[implemented_by]` in \
        {module} (CoreCode), but CoreCode code must be pure and total, so that the proofs are about the code that \
        runs. Remove `@[implemented_by]` from {module}.Coin.tails, then run `lake lint`."])
    s!"a replaced constructor was not named at its own line: {rendered facts}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreSpec.Replaced
  let lake ← lakeOf #[module]
  let unread := emptyChallenge .anonymous ""
  let challenge := { unread with owned := ← readOwned lake unread .build }
  let errors := Statement.ownedViolationErrors lake challenge
  check (errors == #[.ownedViolation (.impure (module ++ `Side.right) .coreSpec [.implementedBy])])
    s!"a CoreSpec constructor with @[implemented_by] was not reported to the owner: {repr errors}"
  let reported := errors.map fun error => (error.message lake default challenge).render
  check (reported == #[s!"SoftwareChallengeTests/Fixtures/CoreSpec/Replaced.lean:9: {module}.Side.right uses \
      `@[implemented_by]` in {module} (CoreSpec), but CoreSpec code must be pure and total, so that the proofs are \
      about the code that runs, and {module} is owned, so no edit to the editable files fixes it. Remove \
      `@[implemented_by]` from {module}.Side.right in SoftwareChallengeTests/Fixtures/CoreSpec/Replaced.lean, and \
      delete owned.lock if there is one, then run `lake build`."])
    s!"a replaced CoreSpec constructor was not named at its own line: {reported}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.Extern
  let facts ← lintFacts module
  check (refusals facts == #[.violation (.impure (module ++ `Coin.tails) .coreCode [.extern])])
    s!"a CoreCode constructor with @[extern] was not refused: {repr (refusals facts)}"
  check (rendered facts == #[
      s!"SoftwareChallengeTests/Fixtures/CoreCode/Extern.lean:9: {module}.Coin.tails uses `@[extern]` in {module} \
        (CoreCode), but CoreCode code must be pure and total, so that the proofs are about the code that runs. \
        Remove `@[extern]` from {module}.Coin.tails, since only a WorldSpec module declares foreign code, and only \
        as an `@[extern] opaque` that computes a value, then run `lake lint`."])
    s!"an extern constructor was not named at its own line: {rendered facts}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `WorldSpec.Extern
  let lake ← lakeOf #[module]
  let unread := emptyChallenge .anonymous ""
  let challenge := { unread with owned := ← readOwned lake unread .build }
  let errors := Statement.ownedViolationErrors lake challenge
  check (errors == #[.ownedViolation (.impure (module ++ `Coin.tails) .worldSpec [.extern]),
      .ownedViolation (.impure (module ++ `Width) .worldSpec [.extern])])
    s!"a WorldSpec constructor or type with @[extern] was not reported to the owner: {repr errors}"
  let reported := errors.map fun error => (error.message lake default challenge).render
  let refusal := fun (line : Nat) (name : String) =>
    s!"SoftwareChallengeTests/Fixtures/WorldSpec/Extern.lean:{line}: {module}.{name} uses `@[extern]` in {module} \
      (WorldSpec), but WorldSpec code may declare foreign code only as an `@[extern] opaque` that computes a value, \
      so that the kernel never unfolds it, and {module} is owned, so no edit to the editable files fixes it. Remove \
      `@[extern]` from {module}.{name}, since only a WorldSpec module declares foreign code, and only as an \
      `@[extern] opaque` that computes a value in SoftwareChallengeTests/Fixtures/WorldSpec/Extern.lean, and delete \
      owned.lock if there is one, then run `lake build`."
  check (reported == #[refusal 9 "Coin.tails", refusal 13 "Width"])
    s!"an extern WorldSpec constructor or type was not named at its own line: {reported}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.Csimp
  let facts ← lintFacts module
  let proof := module ++ `keep_eq_bump
  check ((facts.solution.inventory.declarations.find? (·.name == proof)).any fun fact =>
      fact.isUnsafe && !fact.computational) "the unsafe proof that @[csimp] trusts was misread"
  check (refusals facts == #[.violation (.impure proof .coreCode [.«unsafe»])])
    s!"an unsafe proof that @[csimp] trusts was not refused: {repr (refusals facts)}"
  check (rendered facts == #[
      s!"SoftwareChallengeTests/Fixtures/CoreCode/Csimp.lean:12: {proof} uses `unsafe` in {module} (CoreCode), but \
        CoreCode code must be pure and total, so that the proofs are about the code that runs. Remove `unsafe` from \
        {proof}, then run `lake lint`."])
    s!"an unsafe csimp proof was not named at its own line: {rendered facts}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.UnsafeTerm
  let facts ← lintFacts module
  check (refusals facts == #[.violation (.impure (module ++ `address) .coreCode [.«unsafe»])])
    s!"a CoreCode def that runs an `unsafe` term was not refused: {repr (refusals facts)}"
  check (rendered facts == #[
      s!"SoftwareChallengeTests/Fixtures/CoreCode/UnsafeTerm.lean:7: {module}.address uses `unsafe` in {module} \
        (CoreCode), but CoreCode code must be pure and total, so that the proofs are about the code that runs. \
        Remove `unsafe` from {module}.address, then run `lake lint`."])
    s!"a def that runs an `unsafe` term was not named at its own line: {rendered facts}"

run_cmd Elab.Command.liftCoreM do
  let module := fixture `CoreCode.Generated
  let facts ← lintFacts module
  check (refusals facts == #[])
    s!"a CoreCode declaration that Lean generates was refused: {repr (refusals facts)}"
  let factOf := fun (name : Name) => facts.solution.inventory.declarations.find? fun fact =>
    privateToUserName fact.name == module ++ name
  let generated := [`instBEqRose.beq, `instReprRose.repr, `instOrdRose.ord, `instHashableRose.hash, `instOrdTerm.ord,
    `instDecidableEqTerm.decEq, `instBEqPoint, `Term.ctorIdx, (`Term.ctorIdx).str "_impl", `size._unsafe_rec,
    `halve._unsafe_rec, `countdown._unsafe_rec, `size.eq_1, `Cached.leaf._override, `Cached.total._override,
    `Cached.casesOn, `Term.casesOn, `Term.recOn, `Term.noConfusion, `Point.casesOn]
  let misread := generated.filter fun name => !(factOf name).any fun fact => !fact.written || fact.derived
  check misread.isEmpty s!"declarations that Lean generates were read as written: {misread}"
  let written := [`Rose.node, `Point.x, `Cached.leaf, `Cached.total, `size, `halve, `countdown, `index]
  let unwritten := written.filter fun name => !(factOf name).any fun fact => fact.written && !fact.derived
  check unwritten.isEmpty s!"declarations written in the fixture were read as generated: {unwritten}"
  check ((factOf `instBEqRose.beq).any (·.isPartial) && (factOf `Cached.leaf).any (!·.replaced))
    "a derived partial method or a computed field's constructor was misread"

end

end SoftwareChallengeReadTests.Purity

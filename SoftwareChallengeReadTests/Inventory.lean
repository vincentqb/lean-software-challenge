module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Inventory

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def catalogNames : Array Name :=
  #[`CoreSpec, `WorldSpec, `CoreCode, `WorldCode, `Sibling, `Rejected, `Fixpoint, `Legacy, `Linted, `Corollary,
    `Draft, `Twin, `CoreCode.Derived, `CoreSpec.Derived].map fixture

def rejected (name : Name) : Name := fixture (`Rejected ++ name)

def privately (module name : Name) : Name := (`_private ++ module).num 0 ++ name

def facts (inventory : Inventory) (name : Name) (module : Name := fixture `Rejected) : IO DeclarationFact :=
  match declarationNamed? inventory module name with
  | some fact => pure fact
  | none => throw <| .userError s!"{name} of {module} is missing from the inventory"

run_cmd Elab.Command.liftCoreM do
  let lake ← lakeOf catalogNames
  let imported ← catalogEnv lake .anonymous .lint
  let env := imported.env
  let modules ← catalogModules lake catalogNames imported .lint
  let read ← runIn env (inventoryFacts modules #[fixture `Fixpoint.countdown])
  let inventory := read.inventory
  check (inventory.modules.map (·.name) == catalogNames) "the inventory did not list every catalog module in order"
  check (inventory.modules.all fun module => module.usesModuleSystem == (module.name != fixture `Legacy))
    "a module header was misread: only Legacy.lean has no `module` line"
  check (inventory.modules.all fun module => module.file == sourcePath module.name)
    "a module's file was not the one lake.json names"
  let some worldCode := inventory.modules.find? (·.name == fixture `WorldCode)
    | throwError "WorldCode is missing from the inventory"
  check (worldCode.imports.map (fun i => (i.name, i.comptime, i.line)) == #[(`Init, false, 0), (`Init, true, 0),
      (fixture `CoreCode, false, 3), (fixture `WorldSpec, false, 4), (`SoftwareChallenge, true, 5)])
    s!"WorldCode's imports, their kinds, or their header lines were misread: {repr worldCode.imports}"
  check (Role.ofName (fixture `CoreCode.Derived) == .coreCode && Role.ofName (fixture `CoreSpec.Derived) == .coreSpec &&
      Role.ofName (fixture `Linted) == .tooling) "a role was not read from the module name"
  let unsafeFact ← facts inventory (privately (fixture `Rejected) (rejected `hiddenUnsafe))
  check (unsafeFact.isUnsafe && unsafeFact.computational && unsafeFact.line == 11) "an unsafe def was misread"
  check (← facts inventory (rejected `diverging._unsafe_rec)).isPartial "a partial def's compiled body was not partial"
  check (!(← facts inventory (rejected `diverging)).isPartial) "a partial def's opaque constant was read as partial"
  for (name, module) in [(`halve._unsafe_rec, `CoreCode), (`leafSum._unsafe_rec, `CoreSpec),
      (`Fixpoint.countdown._unsafe_rec, `Fixpoint), (`instBEqRose.beq._unsafe_rec, `CoreCode.Derived),
      (`instBEqForest.beq._unsafe_rec, `CoreSpec.Derived)] do
    let some info := env.find? (fixture name) | throwError "{name} is not in the environment"
    let copy ← facts inventory (fixture name) (fixture module)
    check (info.isPartial && copy.isPartial && !copy.written && copy.copyOf.isSome && !copy.countsAsPartial)
      s!"{name}, which well-founded, structural, terminating partial_fixpoint or derived recursion compiles, was \
        read as a hand-written partial: {repr copy}"
  check (← facts inventory (fixture `Fixpoint.spin._unsafe_rec) (fixture `Fixpoint)).countsAsPartial
    "a partial_fixpoint that no @[terminates] covers was not partial"
  let terminatesNothing ← runIn env (inventoryFacts modules #[])
  let uncovered :=
    declarationNamed? terminatesNothing.inventory (fixture `Fixpoint) (fixture `Fixpoint.countdown._unsafe_rec)
  check (uncovered.any (·.countsAsPartial)) "a partial_fixpoint was exempt though no @[terminates] covers it"
  let rose ← facts inventory (fixture `instBEqRose.beq._unsafe_rec) (fixture `CoreCode.Derived)
  check (rose.copyOf == some (fixture `instBEqRose.beq) && rose.copyOfInstanceMethod)
    s!"a derived instance's compiled copy was misread: {repr rose}"
  let halved ← facts inventory (fixture `halve._unsafe_rec) (fixture `CoreCode)
  check (halved.copyOf == some (fixture `halve) && halved.copyOfTotal && !halved.copyOfInstanceMethod)
    s!"a well-founded function's compiled copy was misread: {repr halved}"
  let countdown ← facts inventory (fixture `Fixpoint.countdown._unsafe_rec) (fixture `Fixpoint)
  check (countdown.copyOfFixpoint && countdown.copyOfTerminated)
    s!"a covered partial_fixpoint's compiled copy was misread: {repr countdown}"
  let bound ← facts inventory (rejected `bound)
  let foreign ← facts inventory (rejected `foreign)
  check (bound.external && bound.unfoldable && foreign.external && !foreign.unfoldable)
    "an extern def or an extern opaque was misread"
  check (← facts inventory (rejected `replaced)).replaced "an implemented_by def was misread"
  let startup ← facts inventory (rejected `startup)
  check (startup.initializes && startup.line == 24) "an initializer was misread"
  check ((← facts inventory (rejected `hiddenEffect)).effects &&
      (← facts inventory (rejected `packagedEffect)).effects &&
      !(← facts inventory (rejected `fast)).effects) "IO through an abbrev or a structure field was misread"
  check ((← facts inventory (rejected `traced)).debug && (← facts inventory (rejected `traceValue)).debug &&
      !(← facts inventory (rejected `fast)).debug) "a dbg builtin was misread"
  let raw := rejected `raw
  for (name, axioms, line) in [(raw, #[raw], 38), (privately (fixture `Rejected) (rejected `viaRaw), #[raw], 40),
      (privately (fixture `Rejected) (rejected `chained), #[raw], 42), (rejected `hole, #[``sorryAx], 44),
      (rejected `viaHole, #[``sorryAx], 46)] do
    let fact ← facts inventory name
    check (fact.axioms == axioms && fact.line == line) s!"{name} was read with axioms {fact.axioms} at line {fact.line}"
  check ((← facts inventory (rejected `decided)).axioms.all fun found => contains found.toString "_native")
    "a native_decide proof's axiom was misread"
  check ((← facts inventory (rejected `EffectBox.mk.injEq)).axioms == #[``propext]) "a standard axiom was not recorded"
  let draft ← facts inventory (fixture `twin_law) (fixture `Draft)
  let twin ← facts inventory (fixture `twin_law) (fixture `Twin)
  check (draft.axioms == #[``sorryAx] && twin.axioms.isEmpty)
    "a theorem two modules declare was not read from each module's own constant"
  let blamed := fun (declaration axiomName culprit : Name) => read.blames.any fun blame =>
    blame.declaration == declaration && blame.axiomName == axiomName && blame.culprit == culprit
  check (blamed (rejected `viaHole) ``sorryAx (rejected `hole) &&
      blamed (privately (fixture `Rejected) (rejected `chained)) raw
        (privately (fixture `Rejected) (rejected `viaRaw)) &&
      blamed (fixture `twin_law) ``sorryAx (fixture `twin_law) && blamed raw raw raw)
    s!"an axiom was blamed on the wrong declaration: {read.blames.map fun blame => (blame.declaration, blame.culprit)}"
  check (read.blames.all (!standardAxioms.contains ·.axiomName)) "a standard axiom was blamed"
  check (inventory.declarations.all fun fact => (env.find? fact.name).isSome)
    "the inventory lists a declaration that the environment lacks"

run_cmd Elab.Command.liftCoreM do
  let lake ← lakeOf catalogNames
  let challenge ← challengeNamed (fixture `Challenge)
  let solution ← readSolution lake challenge .lint
  let callsOf := fun (name : Name) => ((solution.calls.find? (·.1 == name)).map (·.2)).getD #[]
  let reached := fun (name : Name) => Graph.closure (Graph.ofEdges solution.calls) #[name]
  check ((callsOf (fixture `identity)).any (privateToUserName · == fixture `helper) &&
      (reached (fixture `loopIdentity)).contains (fixture `identity) &&
      !(reached (fixture `identity)).contains (fixture `successor))
    "a call was misread: identity calls its private helper, loopIdentity calls identity, and identity never calls \
      successor"
  let proofOf := fun (name : Name) => ((solution.proofUses.find? (·.1 == name)).map (·.2)).getD #[]
  let corollary := fixture `Corollary.corollary
  let bridge := privately (fixture `Corollary) (fixture `Corollary.bridge)
  check ((proofOf corollary).contains bridge && (proofOf bridge).contains (fixture `Corollary.base) &&
      (Graph.closure (Graph.ofEdges solution.proofUses) #[corollary]).contains (fixture `Corollary.base))
    s!"corollary does not reach base through its private lemma: {proofOf corollary}"
  check ((solution.meanings.find? (·.1 == fixture `Rejected.Effect)).any (·.2.contains ``IO) &&
      (Graph.dependingOn (Graph.ofEdges solution.meanings) #[``IO.RealWorld]).contains (fixture `Rejected.Effect))
    "the meanings that give effects were misread"
  check (solution.imports.any fun line => line.module == fixture `Rejected && line.fact.name == fixture `WorldSpec &&
      line.fact.line == 4 && line.text == "public import SoftwareChallengeTests.Fixtures.WorldSpec")
    "an import line of the catalog was misread"
  check (solution.sorries.map (fun place => (place.file, place.line)) ==
      #[("SoftwareChallengeTests/Fixtures/Rejected.lean", 44), ("SoftwareChallengeTests/Fixtures/Draft.lean", 7)])
    s!"the sorries were misread: {solution.sorries.map (·.line)}"
  check (solution.lints.map (fun lint => (lint.module, lint.place.file, lint.place.line, lint.linter)) ==
      #[(fixture `Linted, "SoftwareChallengeTests/Fixtures/Linted.lean", 7, `linter.unusedVariables)] &&
      solution.lints.all (contains ·.message "Variable name `h` is not explicitly referenced"))
    s!"the linter warnings were misread: {solution.lints.map (·.message)}"
  check (solution.linted == catalogNames) "a catalog module's linter warnings were not read"
  check (solution.inventory.modules.any (·.name == fixture `Linted) &&
      !solution.inventory.modules.any fun module => module.imports.any (·.name == fixture `Linted))
    "Linted.lean, which only a glob reaches, was not read"
  check (solution.fixpoints.size == 2 && solution.fixpoints.contains (fixture `Fixpoint.spin) &&
    solution.fixpoints.contains (fixture `Fixpoint.countdown)) s!"the fixpoints were misread: {solution.fixpoints}"
  check solution.main?.isNone "a main was read where no module defines one"
  check (solution.places.any fun found => found.name == rejected `startup && found.place.line == 24 &&
      found.written == "startup" && found.firstLine == "initialize startup : Nat ← pure 0")
    "a declaration's place, written name, or first line was misread"
  check (solution.registrations.any fun registration => registration.claim == fixture `Identity &&
      registration.module == fixture `Rejected && registration.home? == some (fixture `WorldSpec) &&
      registration.place.line == 0) "the claimsExt entry Rejected forges was not read"
  check (solution.registrations.any fun registration => registration.claim == fixture `SuccAgrees &&
      registration.module == fixture `WorldSpec && registration.home? == some (fixture `WorldSpec) &&
      registration.place.line == 14) "a WorldClaim's registration was misread"
  check (solution.registrations.any fun registration => registration.claim == fixture `CoreClaim &&
      registration.module == fixture `CoreCode) "a WorldClaim outside WorldSpec was not read"

end

end SoftwareChallengeReadTests.Inventory

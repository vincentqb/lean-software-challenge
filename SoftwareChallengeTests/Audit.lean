module

import all SoftwareChallengeTests.Fixtures.CoreSpec
import all SoftwareChallengeTests.Fixtures.WorldSpec
import all SoftwareChallengeTests.Fixtures.CoreCode
import all SoftwareChallengeTests.Fixtures.WorldCode
import all SoftwareChallengeTests.Fixtures.Sibling
import all SoftwareChallengeTests.Fixtures.Rejected
import all SoftwareChallengeTests.Fixtures.Fixpoint
import SoftwareChallengeTests.Fixtures.Challenge
meta import SoftwareChallenge.Audit
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Audit

meta section

open Lean SoftwareChallenge

private def fixture (name : Name) : Name := `SoftwareChallengeTests.Fixtures ++ name

private def project : Project := {
  modules := #[(fixture `CoreSpec, .coreSpec), (fixture `WorldSpec, .worldSpec),
    (fixture `CoreCode, .coreCode), (fixture `WorldCode, .worldCode), (fixture `Sibling, .worldCode), (fixture `Rejected, .coreCode),
    (fixture `Fixpoint, .coreCode)]
}

private def valid : Array Name :=
  #[fixture `CoreSpec, fixture `WorldSpec, fixture `CoreCode, fixture `WorldCode, fixture `Sibling]

private def countdown : Name := fixture `Fixpoint.countdown

private def countdownTerminates : Name := fixture `Fixpoint.countdown_terminates

private def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

private def expect (errors : Array String) (name reason : String) : CoreM Unit := do
  unless errors.any (fun error => contains error name && contains error reason) do
    throwError "Missing rejection of {name}: {reason}\n{errors}"

private def violations (project : Project) (inventory : Inventory) : Array String :=
  Audit.sound project { inventory }

private def expectedConfig : String := "{
  \"challenge_module\": \"Challenge\",
  \"solution_module\": \"A.Solution\",
  \"theorem_names\": [
    \"SoftwareChallengeTests.Fixtures.Challenge.double_even\",
    \"SoftwareChallengeTests.Fixtures.Challenge.double_even_rejects_identity\",
    \"SoftwareChallengeTests.Fixtures.Challenge.double_even_rejects_nothing\",
    \"SoftwareChallengeTests.Fixtures.Challenge.triple_rejects_nothing\",
    \"SoftwareChallengeTests.Fixtures.Challenge.double_zero\",
    \"SoftwareChallengeTests.Fixtures.Challenge.double_one\",
    \"SoftwareChallengeTests.Fixtures.Challenge.double_one_rejects_one\"
  ],
  \"definition_names\": [
    \"SoftwareChallengeTests.Fixtures.Challenge.double\"
  ],
  \"permitted_axioms\": [
    \"propext\",
    \"Classical.choice\",
    \"Quot.sound\"
  ]
}
"

#guard Role.ofName `A.CoreCode.B == .coreCode
#guard Role.ofName `A.WorldSpec.CoreCode == .worldSpec
#guard Role.ofName `A.Helpers == .tooling
#guard Role.ofName `A.CoreCodeHelpers == .tooling

#guard
  let layout := Project.ofPackage #[`A.CoreCode.B, `A.Helpers, `A.WorldSpec] false
  !layout.admits .coreCode { name := `A.Helpers, comptime := false } &&
    !layout.admits .coreCode { name := `A.WorldSpec, comptime := false } &&
    layout.admits .coreCode { name := `A.WorldSpec, comptime := true } &&
    layout.admits .coreCode { name := `Lean.Data.Name, comptime := false } &&
    layout.role? `A.CoreCode.B == some .coreCode && layout.role? `Lean.Data.Name == none

run_cmd Elab.Command.liftCoreM do
  let accepted ← Audit.collect valid
  unless project.check accepted do
    throwError "Valid fixtures were rejected:\n{violations project accepted}"
  let reassign (module : Name) (role : Role) : Project :=
    { modules := project.modules.map fun (name, r) => (name, if name == module then role else r) }
  let rejected ← Audit.collect (valid.push (fixture `Rejected))
  for layout in #[project, reassign (fixture `Rejected) .coreSpec] do
    if layout.check rejected then throwError "Rejected fixtures passed"
    for (name, reason) in #[("hiddenUnsafe", "unsafe"), ("diverging", "partial"),
        ("hiddenEffect", "IO"), ("packagedEffect", "IO"), ("startup", "initializer"),
        ("bound", "@[extern]"), ("Rejected.foreign", "@[extern]"), ("Rejected.replaced", "@[implemented_by]"),
        ("traced", "dbg builtin"), ("traceValue", "dbg builtin"), ("Rejected.raw", "uses axiom"),
        ("chained", "Rejected.raw"), ("Rejected.hole", "sorryAx"),
        ("Fixtures.Rejected", "may not import SoftwareChallengeTests.Fixtures.WorldSpec (WorldSpec)")] do
      expect (violations layout rejected) name reason
    if (violations layout rejected).any (contains · "_unsafe_rec") then
      throwError "A partial definition was reported by its compiler name"
  for (module, role, facts, name, reason) in #[
      (fixture `CoreSpec, Role.coreCode, accepted, "Fixtures.WorldSpec", "may not import"),
      (fixture `WorldCode, .worldSpec, accepted, "Fixtures.WorldCode", "may not import"),
      (fixture `WorldCode, .worldSpec, accepted, "drain", "partial"),
      (fixture `CoreCode, .tooling, accepted, "Fixtures.WorldCode", "may not import"),
      (fixture `Rejected, .worldCode, rejected, "hiddenUnsafe", "unsafe"),
      (fixture `Rejected, .worldCode, rejected, "bound", "@[extern]"),
      (fixture `Rejected, .worldCode, rejected, "Rejected.foreign", "@[extern]"),
      (fixture `Rejected, .worldCode, rejected, "Rejected.replaced", "@[implemented_by]"),
      (fixture `Rejected, .tooling, rejected, "Rejected.raw", "uses axiom"),
      (fixture `Rejected, .worldSpec, rejected, "bound", "@[extern] with a body the kernel unfolds"),
      (fixture `Rejected, .worldSpec, rejected, "hiddenEffect", "IO")] do
    expect (violations (reassign module role) facts) name reason
  if (violations (reassign (fixture `Rejected) .worldSpec) rejected).any (contains · "Rejected.foreign") then
    throwError "An @[extern] opaque declaration was rejected in a WorldSpec module"
  let fixpoints := valid.push (fixture `Fixpoint)
  let unproved ← Audit.collect fixpoints
  if project.check unproved then throwError "A partial_fixpoint without a termination headline passed"
  expect (violations project unproved) "Fixpoint.countdown" "partial"
  let covered ← Audit.collect fixpoints (NameSet.empty.insert countdown)
  expect (violations project covered) "Fixpoint.spin" "partial"
  if (violations project covered).any (contains · "countdown") then
    throwError "A partial_fixpoint with a termination headline was reported partial"
  let listedPartial ← Audit.collect (valid.push (fixture `Rejected))
    (NameSet.empty.insert (fixture `Rejected.diverging))
  expect (violations project listedPartial) "diverging" "partial"
  let legacy := { accepted with
    modules := accepted.modules.map ({ · with usesModuleSystem := false }) }
  if project.check legacy then throwError "A file without `module` passed"
  expect (violations project legacy) "Fixtures.CoreCode" "start the file with `module`"
  let outside : Project := { modules := project.modules.filter (·.1 != fixture `WorldCode) }
  if outside.check accepted then throwError "A module outside the package was audited as one of it"
  expect (violations outside accepted) "Fixtures.WorldCode" "not a module of the challenge package"
  let challenge := Audit.owned project {
    challengeImports := ← Audit.challengeImports "SoftwareChallengeTests/Fixtures/Challenge.lean" }
  expect challenge "Fixtures.CoreCode" "may import only CoreSpec and WorldSpec"
  if challenge.any (contains · "imports SoftwareChallenge;") then
    throwError "A challenge import from outside the package was rejected: {challenge}"
  let locked := #[("Challenge.lean", (1 : UInt64)), ("CoreSpec.lean", 2), ("Gone.lean", 3)]
  let drifted := Audit.lockErrors locked #[("Challenge.lean", 1), ("CoreSpec.lean", 5), ("New.lean", 4)]
    #["CoreCode.lean"]
  expect drifted "CoreSpec.lean changed" "edit CoreCode.lean instead"
  expect drifted "New.lean" "does not record it"
  expect drifted "Gone.lean" "missing"
  if drifted.any (contains · "Challenge.lean") then throwError "An unchanged owned file was reported"
  let env ← getEnv
  let reached := Audit.reachedFrom env fun name =>
    (env.getModuleIdxFor? name).any (valid.contains env.header.modules[·.toNat]!.module)
  unless (reached (fixture `identity)).toList.any (privateToUserName · == fixture `helper) &&
      !(reached (fixture `identity)).contains (fixture `successor) &&
      (reached (fixture `loopIdentity)).contains (fixture `identity) do
    throwError "Runtime reachability misread a call"
  expect (Audit.sound project { entry := some (some (fixture `WorldCode), #[`h]) }) "h" "main never reaches"
  expect (Audit.sound project { entry := some (some (fixture `CoreCode), #[]) }) "main" "WorldCode module"
  let moduleOf := fun (_ : Name) => some (fixture `WorldCode)
  let missing := Audit.entryOf { project with executable := true } env moduleOf (fun _ => true) #[`h]
  unless missing matches some (none, #[]) do throwError "A missing main passed"
  expect (Audit.sound project { entry := missing }) "main" "declares a lean_exe"
  if (Audit.entryOf project env moduleOf (fun _ => true) #[`h]).isSome then
    throwError "A library without a lean_exe was required to have a main"
  let registrations := (valid.push (fixture `Rejected)).flatMap fun module =>
    (PersistentEnvExtension.getModuleEntries claimsExt env (env.getModuleIdx? module).get!).map
      fun claim => (claim, project.role? module, (env.getModuleIdxFor? claim).any
        (env.header.modules[·.toNat]!.module == module))
  let registered := Audit.owned project { registrations }
  expect registered "CoreClaim" "declare WorldClaims in a WorldSpec module"
  expect registered "Identity" "registered outside the module that declares it"
  if registered.any (contains · "SuccAgrees") then
    throwError "A claim declared in a WorldSpec module was rejected: {registered}"

run_cmd Elab.Command.liftTermElabM do
  let evidence := allEvidence (← getEnv)
  let world ← Audit.headline evidence (fixture `successor_grows)
  let precondition ← Audit.headline evidence (fixture `bounded)
  unless world.assumptions.map (·.claim) == #[fixture `SuccAgrees] do throwError "A world claim was misread"
  unless (evidence.filter (·.claim == fixture `SuccAgrees)).size == 3 && world.assumptions.map (·.checks) == #[2] do
    throwError "A Check of another instance of a claim counted"
  unless precondition.assumptions.isEmpty && precondition.unnamed.isEmpty do
    throwError "A precondition was read as an assumption"
  let missing ← try discard <| Audit.headline evidence `SoftwareChallengeTests.Missing; pure false
    catch _ => pure true
  unless missing do throwError "A missing headline passed"
  let headlines ← #[fixture `uses_unchecked, fixture `uses_live, fixture `uses_unnamed].mapM
    fun name => Audit.headline evidence name
  let facts : Audit.Facts := {
    headlines := headlines.push world
    holes := #[(fixture `SuccAgrees, some (fixture `WorldSpec))] }
  let errors := Audit.sound project facts ++ Audit.evidenced facts
  expect errors "Unchecked" "has no Check"
  expect errors "SuccAgrees" "defined in SoftwareChallengeTests.Fixtures.WorldSpec (WorldSpec)"
  expect errors "uses_unnamed" "not a WorldClaim"
  if errors.any (fun e => contains e "ClockAdvances" || contains e "SuccAgrees has no Check") then
    throwError "Checks did not count: {errors}"
  let env ← getEnv
  let replaceable := NameSet.empty.insert (fixture `identity)
  unless Audit.kills env replaceable (fixture `identity_fixed) (fixture `identity_fixed_rejects_successor) do
    throwError "A kill was not recognised"
  if Audit.kills env replaceable (fixture `identity_fixed) (fixture `mismatched_negation) then
    throwError "A different statement counted as a kill"
  unless Audit.kills env replaceable (fixture `identity_three) (fixture `identity_three_rejects_successor) do
    throwError "A kill of a headline about a concrete argument was not recognised"
  unless Audit.kills env replaceable (fixture `identity_twice) (fixture `identity_twice_rejects_successor) do
    throwError "A kill that replaces a nested hole by a lambda was not recognised"
  if Audit.kills env replaceable (fixture `identity_twice) (fixture `identity_twice_rejects_mixed) then
    throwError "A kill that replaces one hole by two different functions counted"
  let foreign := (NameSet.empty.insert (fixture `successor)).insert (fixture `nativeSucc)
  unless Audit.kills env foreign (fixture `successor_correct) (fixture `successor_correct_rejects_identity) do
    throwError "A kill that replaces a foreign constant was not recognised"
  if Audit.kills env (NameSet.empty.insert (fixture `successor)) (fixture `successor_correct)
      (fixture `successor_correct_rejects_identity) then
    throwError "A kill that replaces a constant that is not replaceable counted"
  let killed : Audit.Challenge := {
    theorems := #[fixture `identity_fixed, fixture `identity_fixed_rejects_successor, fixture `bounded]
    kills := #[(fixture `identity_fixed_rejects_successor, fixture `identity_fixed)] }
  unless killed.headlines == #[fixture `identity_fixed, fixture `bounded] do
    throwError "A kill was reported as a headline: {killed.headlines}"
  expect (Audit.meaningful { challenge := killed }) "bounded" "no kill"
  expect (Audit.meaningful { holes := #[(`h, none)] }) "h" "no headline mentions this hole"
  if (Audit.meaningful { challenge := killed }).any (contains · "identity_fixed") then
    throwError "A killed headline was reported unkilled"
  let stuck := fixture `Fixpoint.countdown_terminates_rejects_stuck
  let termination := fun (definition headline : Name) => Audit.sound project {
    challenge := { theorems := #[countdownTerminates, stuck, fixture `bounded]
                   kills := #[(stuck, countdownTerminates)] }
    holes := #[(countdown, some (fixture `Fixpoint)), (fixture `identity, some (fixture `CoreCode))]
    terminations := Audit.terminations env #[(definition, headline)] }
  unless (termination countdown countdownTerminates).isEmpty do
    throwError "A listed termination headline was rejected: {termination countdown countdownTerminates}"
  expect (termination (fixture `Fixpoint.spin) countdownTerminates) "spin" "not a definition hole"
  expect (termination (fixture `Fixpoint.spin) countdownTerminates) "spin" "does not mention it"
  expect (termination (fixture `identity) (fixture `identity_fixed)) "identity" "not a partial_fixpoint definition"
  expect (termination countdown (fixture `Fixpoint.countdown_terminates_rejects_stuck)) "countdown"
    "not a headline with a kill"
  expect (termination countdown (fixture `bounded)) "countdown" "not a headline with a kill"
  expect (termination countdown (fixture `bounded)) "bounded" "does not mention it"
  let marked ← Audit.readChallenge project (fixture `Challenge)
  let member := fun (name : Name) => fixture (`Challenge ++ name)
  unless marked.theorems == #[member `double_even, member `double_even_rejects_identity,
      member `double_even_rejects_nothing, member `triple_rejects_nothing, member `double_zero, member `double_one,
      member `double_one_rejects_one] &&
      marked.holes == #[member `double] && marked.filled == #[member `triple] &&
      marked.terminating == #[(member `triple, member `double_zero)] do
    throwError "The challenge was misread: {marked.theorems} {marked.holes} {marked.filled} {marked.terminating}"
  let markedFacts : Audit.Facts := {
    challenge := marked
    holes := marked.holes.map (·, some (fixture `CoreCode))
    terminations := Audit.terminations env marked.terminating }
  let misread := Audit.meaningful markedFacts
  expect misread "double_zero" "no kill"
  expect misread "double_one:" "mark SoftwareChallengeTests.Fixtures.Challenge.double_one_rejects_one `@[kills"
  if misread.any (contains · "double_one_rejects_one: no kill") then
    throwError "An unmarked kill was reported as a headline without a kill: {misread}"
  expect misread "double_even_rejects_nothing" "but it is not `¬` SoftwareChallengeTests.Fixtures.Challenge.double_even"
  expect misread "triple_rejects_nothing" "is not a headline of Challenge.lean"
  if misread.any fun error => contains error "double_even:" || contains error "rejects_identity" then
    throwError "A marked kill was rejected: {misread}"
  expect (Audit.sound project markedFacts) "triple" "but it is not a definition hole"
  expect (Audit.owned project markedFacts) "implements SoftwareChallengeTests.Fixtures.Challenge.triple"
    "implement it in a CoreCode or WorldCode module"
  unless (Audit.solutionOf #[`A.CoreCode, `A.Solution]).toOption == some `A.Solution do
    throwError "The Solution module was not found"
  for catalog in #[#[`A.CoreCode], #[`A.Solution, `B.Solution]] do
    let .error error := Audit.solutionOf catalog | throwError "{catalog} named one Solution module"
    unless contains error "name only the module that proves the headlines and kills Solution" ||
        contains error "name the module that proves the headlines and kills Solution" do
      throwError "A Solution error was unclear: {error}"
  let generated := Audit.comparatorConfig `A.Solution marked
  unless generated == expectedConfig do throwError "Generated comparator.json:\n{generated}"

end

end SoftwareChallengeTests.Audit

module

import all SoftwareChallengeTests.Fixtures.Spec
import all SoftwareChallengeTests.Fixtures.Core
import all SoftwareChallengeTests.Fixtures.Shell
import all SoftwareChallengeTests.Fixtures.Rejected
import all SoftwareChallengeTests.Fixtures.Fixpoint
meta import SoftwareChallenge.Audit
public meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Audit

open SoftwareChallengeTests.Fixtures

Test Identity identity : identity 5 = 5 := by decide

meta section

open Lean SoftwareChallenge

private def project : Project := {
  layers := #[(`SoftwareChallengeTests.Fixtures.Spec, .spec),
    (`SoftwareChallengeTests.Fixtures.Boundary, .boundary), (`SoftwareChallengeTests.Fixtures.Core, .core),
    (`SoftwareChallengeTests.Fixtures.Shell, .shell), (`SoftwareChallengeTests.Fixtures.Rejected, .core),
    (`SoftwareChallengeTests.Fixtures.Fixpoint, .core)]
}

private def valid : Array Name := #[`SoftwareChallengeTests.Fixtures.Boundary,
  `SoftwareChallengeTests.Fixtures.Spec, `SoftwareChallengeTests.Fixtures.Core,
  `SoftwareChallengeTests.Fixtures.Shell]

private def countdown : Name := `SoftwareChallengeTests.Fixtures.Fixpoint.countdown

private def countdownTerminates : Name := `SoftwareChallengeTests.Fixtures.Fixpoint.countdown_terminates

private def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

private def expect (errors : Array String) (name reason : String) : CoreM Unit := do
  unless errors.any (fun error => contains error name && contains error reason) do
    throwError "Missing rejection of {name}: {reason}\n{errors}"

private def violations (project : Project) (inventory : Inventory) : Array String :=
  Audit.sound project { inventory }

private def config : Audit.Config := {
  challenge_module := `SoftwareChallengeTests.Fixtures.Challenge
  solution_module := `SoftwareChallengeTests.Fixtures.Core
  theorem_names := #[`A]
  definition_names := some #[`h] }

#guard ({ layers := #[(`A, .tooling), (`A.B.C, .core), (`A.B, .spec)] } : Project).role?
  `A.B.C.D == some .core

run_cmd Elab.Command.liftCoreM do
  let accepted ← Audit.collect valid
  unless project.check accepted do
    throwError "Valid fixtures were rejected:\n{violations project accepted}"
  let reassign (module : Name) (role : Role) : Project :=
    { layers := project.layers.map fun (name, r) => (name, if name == module then role else r) }
  let rejected ← Audit.collect (valid.push `SoftwareChallengeTests.Fixtures.Rejected)
  for layout in #[project, reassign `SoftwareChallengeTests.Fixtures.Rejected .spec] do
    if layout.check rejected then throwError "Rejected fixtures passed"
    for (name, reason) in #[("hiddenUnsafe", "unsafe"), ("diverging", "partial"),
        ("hiddenEffect", "IO"), ("packagedEffect", "IO"), ("startup", "initializer"),
        ("bound", "@[extern]"), ("Rejected.replaced", "@[implemented_by]"),
        ("traced", "dbg builtin"), ("traceValue", "dbg builtin"), ("Rejected.raw", "axioms"),
        ("chained", "Rejected.raw"), ("Rejected.hole", "sorryAx"),
        ("Fixtures.Rejected", "may not import")] do
      expect (violations layout rejected) name reason
  for (module, role, facts, name, reason) in #[
      (`SoftwareChallengeTests.Fixtures.Core, Role.boundary, accepted, "identity",
        "not an @[extern] binding"),
      (`SoftwareChallengeTests.Fixtures.Boundary, .core, accepted, "Fixtures.Spec", "may not import"),
      (`SoftwareChallengeTests.Fixtures.Shell, .boundary, accepted, "Fixtures.Shell", "may not import"),
      (`SoftwareChallengeTests.Fixtures.Core, .tooling, accepted, "Fixtures.Shell", "may not import"),
      (`SoftwareChallengeTests.Fixtures.Rejected, .shell, rejected, "hiddenUnsafe", "unsafe"),
      (`SoftwareChallengeTests.Fixtures.Rejected, .shell, rejected, "bound", "@[extern]"),
      (`SoftwareChallengeTests.Fixtures.Rejected, .shell, rejected, "Rejected.replaced",
        "@[implemented_by]"),
      (`SoftwareChallengeTests.Fixtures.Rejected, .tooling, rejected, "Rejected.raw", "axioms"),
      (`SoftwareChallengeTests.Fixtures.Rejected, .boundary, rejected, "bound",
        "@[extern] with a body the kernel unfolds")] do
    expect (violations (reassign module role) facts) name reason
  let fixpoints := valid.push `SoftwareChallengeTests.Fixtures.Fixpoint
  let unproved ← Audit.collect fixpoints
  if project.check unproved then throwError "A partial_fixpoint without a termination headline passed"
  expect (violations project unproved) "Fixpoint.countdown" "partial"
  let covered ← Audit.collect fixpoints (NameSet.empty.insert countdown)
  expect (violations project covered) "Fixpoint.spin" "partial"
  if (violations project covered).any (contains · "countdown") then
    throwError "A partial_fixpoint with a termination headline was reported partial"
  let listedPartial ← Audit.collect (valid.push `SoftwareChallengeTests.Fixtures.Rejected)
    (NameSet.empty.insert `SoftwareChallengeTests.Fixtures.Rejected.diverging)
  expect (violations project listedPartial) "diverging" "partial"
  let legacy := { accepted with
    modules := accepted.modules.map ({ · with usesModuleSystem := false }) }
  if project.check legacy then throwError "A file without `module` passed"
  expect (violations project legacy) "Fixtures.Core" "start the file with `module`"
  let unlisted : Project :=
    { layers := project.layers.filter (·.1 != `SoftwareChallengeTests.Fixtures.Shell) }
  if unlisted.check accepted then throwError "An unclassified module passed"
  expect (violations unlisted accepted) "Fixtures.Shell" "Unclassified"
  let challenge := Audit.owned project config {
    challengeTheorems := #[`A]
    challengeHoles := #[`h]
    challengeImports := ← Audit.challengeImports `SoftwareChallengeTests.Fixtures.Challenge }
  expect challenge "Fixtures.Core" "may import only spec and boundary"
  expect challenge "imports SoftwareChallenge;" "may import only spec and boundary"
  let listing := Audit.owned project config { challengeTheorems := #[`A, `B], challengeHoles := #[`g] }
  expect listing "declares B" "theorem_names omits"
  expect listing "declares g" "definition_names omits"
  expect listing "lists h" "does not declare"
  let filled := Audit.owned project config
    { challengeTheorems := #[`A], challengeHoles := #[], challengeFilled := #[`h] }
  expect filled "implements h" "implement it in a core or shell module"
  if filled.any (contains · "does not declare") then
    throwError "A filled hole was reported undeclared: {filled}"
  let locked := #[("Challenge.lean", (1 : UInt64)), ("Spec.lean", 2), ("Gone.lean", 3)]
  let drifted := Audit.lockErrors locked #[("Challenge.lean", 1), ("Spec.lean", 5), ("New.lean", 4)]
    #["Core.lean"]
  expect drifted "Spec.lean changed" "edit Core.lean instead"
  expect drifted "New.lean" "does not record it"
  expect drifted "Gone.lean" "missing"
  if drifted.any (contains · "Challenge.lean") then throwError "An unchanged owned file was reported"
  let env ← getEnv
  let reached := Audit.reachedFrom env fun name =>
    (env.getModuleIdxFor? name).any (valid.contains env.header.modules[·.toNat]!.module)
  unless (reached `SoftwareChallengeTests.Fixtures.identity).toList.any
      (privateToUserName · == `SoftwareChallengeTests.Fixtures.helper) &&
      !(reached `SoftwareChallengeTests.Fixtures.identity).contains `SoftwareChallengeTests.Fixtures.successor &&
      (reached `SoftwareChallengeTests.Fixtures.loopIdentity).contains `SoftwareChallengeTests.Fixtures.identity do
    throwError "Runtime reachability misread a call"
  expect (Audit.sound project { entry := some (`main, some .shell, #[`h]) }) "h" "main never reaches"
  expect (Audit.sound project { entry := some (`main, some .tooling, #[]) }) "main" "shell module"
  let roleOf := fun (_ : Name) => some Role.shell
  let missing := Audit.entryOf project env roleOf (fun _ => true) #[`h]
  unless missing matches some (`main, none, #[]) do throwError "A missing main passed"
  expect (Audit.sound project { entry := missing }) "main" "shell module"
  if (Audit.entryOf { project with entry := none } env roleOf (fun _ => true) #[`h]).isSome then
    throwError "A library without an entry was required to have one"
  let registrations := (valid.push `SoftwareChallengeTests.Fixtures.Rejected).flatMap fun module =>
    (PersistentEnvExtension.getModuleEntries claimsExt env (env.getModuleIdx? module).get!).map
      fun (claim, _) => (claim, project.role? module, (env.getModuleIdxFor? claim).any
        (env.header.modules[·.toNat]!.module == module))
  let registered := Audit.owned project config
    { registrations, challengeTheorems := #[`A], challengeHoles := #[`h] }
  expect registered "CoreClaim" "declare claims in a spec module"
  expect registered "Identity" "registered outside the module that declares it"

run_cmd Elab.Command.liftTermElabM do
  let listed := #[`SoftwareChallengeTests.Fixtures.even_four]
  let world ← Audit.headline listed `SoftwareChallengeTests.Fixtures.successor_grows
  let open_ ← Audit.headline listed `SoftwareChallengeTests.Fixtures.uses_open
  let discharged ← Audit.headline listed `SoftwareChallengeTests.Fixtures.uses_discharged
  let unlistedProof ← Audit.headline #[] `SoftwareChallengeTests.Fixtures.uses_discharged
  let precondition ← Audit.headline listed `SoftwareChallengeTests.Fixtures.bounded
  unless world.premises.map (·.claim) == #[`SoftwareChallengeTests.Fixtures.SuccAgrees] &&
      proved world.premises do
    throwError "A world premise was misread"
  if proved open_.premises then throwError "An open conjecture was reported proved"
  unless proved discharged.premises &&
      discharged.premises.all (·.dischargedBy == some `SoftwareChallengeTests.Fixtures.even_four) do
    throwError "A proved conjecture was not recognised"
  if proved unlistedProof.premises then
    throwError "A conjecture counted as proved by a theorem comparator.json does not list"
  unless precondition.premises.isEmpty && precondition.unnamed.isEmpty do
    throwError "A precondition was read as an assumption"
  let missing ← try discard <| Audit.headline listed `SoftwareChallengeTests.Missing; pure false catch _ => pure true
  unless missing do throwError "A missing headline passed"
  let headlines ← #[`SoftwareChallengeTests.Fixtures.uses_unchecked,
    `SoftwareChallengeTests.Fixtures.uses_live, `SoftwareChallengeTests.Fixtures.uses_unnamed].mapM
    fun name => Audit.headline listed name
  let facts : Audit.Facts := {
    headlines := headlines.push world
    evidence := allEvidence (← getEnv)
    holes := #[(`SoftwareChallengeTests.Fixtures.EvenFour, some .spec)] }
  let errors := Audit.sound project facts ++ Audit.evidenced facts
  expect errors "Unchecked" "no Test, Check, or live suite"
  expect errors "EvenFour" "core or shell definition"
  expect errors "uses_unnamed" "not a WorldClaim or Conjecture"
  if errors.any (fun e => contains e "ClockAdvances" || contains e "SuccAgrees") then
    throwError "Evidence did not count: {errors}"
  let replaceable := NameSet.empty.insert `SoftwareChallengeTests.Fixtures.identity
  unless ← Audit.kills replaceable `SoftwareChallengeTests.Fixtures.identity_fixed
      `SoftwareChallengeTests.Fixtures.identity_fixed_rejects_successor do
    throwError "A kill was not recognised"
  if ← Audit.kills replaceable `SoftwareChallengeTests.Fixtures.identity_fixed
      `SoftwareChallengeTests.Fixtures.mismatched_negation then
    throwError "A different statement counted as a kill"
  unless ← Audit.kills replaceable `SoftwareChallengeTests.Fixtures.identity_three
      `SoftwareChallengeTests.Fixtures.identity_three_rejects_successor do
    throwError "A kill of a headline about a concrete argument was not recognised"
  let killed ← Audit.killsOf replaceable #[`SoftwareChallengeTests.Fixtures.identity_fixed,
    `SoftwareChallengeTests.Fixtures.identity_fixed_rejects_successor, `SoftwareChallengeTests.Fixtures.bounded]
  unless killed.map (·.1) == #[`SoftwareChallengeTests.Fixtures.identity_fixed,
      `SoftwareChallengeTests.Fixtures.bounded] do
    throwError "A kill was reported as a headline: {killed.map (·.1)}"
  expect (Audit.meaningful { killsByHeadline := killed }) "bounded" "no kill"
  expect (Audit.meaningful { holes := #[(`h, none)] }) "h" "no headline mentions this hole"
  if (Audit.meaningful { killsByHeadline := killed }).any (contains · "identity_fixed") then
    throwError "A killed headline was reported unkilled"
  let fixpointKills ← Audit.killsOf (NameSet.empty.insert countdown) #[countdownTerminates,
    `SoftwareChallengeTests.Fixtures.Fixpoint.countdown_terminates_rejects_stuck,
    `SoftwareChallengeTests.Fixtures.bounded]
  let env ← getEnv
  let termination := fun (definition headline : Name) => Audit.sound project {
    killsByHeadline := fixpointKills
    holes := #[(countdown, some .core), (`SoftwareChallengeTests.Fixtures.identity, some .core)]
    terminations := Audit.terminations env { config with
      definition_names := some #[countdown, `SoftwareChallengeTests.Fixtures.identity]
      terminates := some (({} : NameMap Name).insert definition headline) } }
  unless (termination countdown countdownTerminates).isEmpty do
    throwError "A listed termination headline was rejected: {termination countdown countdownTerminates}"
  expect (termination `SoftwareChallengeTests.Fixtures.Fixpoint.spin countdownTerminates) "spin"
    "not a definition hole"
  expect (termination `SoftwareChallengeTests.Fixtures.Fixpoint.spin countdownTerminates) "spin"
    "does not mention it"
  expect (termination `SoftwareChallengeTests.Fixtures.identity `SoftwareChallengeTests.Fixtures.identity_fixed)
    "identity" "not a partial_fixpoint definition"
  expect (termination countdown `SoftwareChallengeTests.Fixtures.Fixpoint.countdown_terminates_rejects_stuck)
    "countdown" "not a headline with a kill"
  expect (termination countdown `SoftwareChallengeTests.Fixtures.bounded) "countdown" "not a headline with a kill"
  expect (termination countdown `SoftwareChallengeTests.Fixtures.bounded) "bounded" "does not mention it"

end

end SoftwareChallengeTests.Audit

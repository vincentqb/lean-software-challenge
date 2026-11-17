module

import all SoftwareChallengeTests.Fixtures.CoreSpec
import all SoftwareChallengeTests.Fixtures.WorldSpec
import all SoftwareChallengeTests.Fixtures.CoreCode
import all SoftwareChallengeTests.Fixtures.WorldCode
import all SoftwareChallengeTests.Fixtures.Sibling
import all SoftwareChallengeTests.Fixtures.Rejected
import all SoftwareChallengeTests.Fixtures.Fixpoint
import SoftwareChallengeTests.Fixtures.Challenge
import SoftwareChallengeTests.Fixtures.WitnessChallenge
meta import SoftwareChallenge.Audit
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Audit

private theorem double_negative_vanishes_has_no_witness :
    ¬ ∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n < 0 :=
  fun ⟨_, below⟩ => Nat.not_lt_zero _ below

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
    \"SoftwareChallengeTests.Fixtures.Challenge.double_even_independent\",
    \"SoftwareChallengeTests.Fixtures.Challenge.double_even_partly_independent\",
    \"SoftwareChallengeTests.Fixtures.Challenge.double_even_independent_mixed\",
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

run_cmd Elab.Command.liftCoreM do
  let challenge := fixture `Challenge
  let olean ← findOLean challenge
  let some library := (olean.parent.bind (·.parent)).bind (·.parent) | throwError "{olean} has no library"
  let dependency ← IO.FS.createTempDir
  let shadow := dependency / "SoftwareChallengeTests" / "Fixtures" / "Challenge.olean"
  let saved ← searchPathRef.get
  try
    for file in ← (library / "SoftwareChallengeTests").walkDir do
      unless ← file.isDir do
        let some relative := file.toString.dropPrefix? library.toString | throwError "{file} is outside {library}"
        let copy : System.FilePath := dependency.toString ++ relative.toString
        IO.FS.createDirAll (copy.parent.getD dependency)
        IO.FS.writeBinFile copy (← IO.FS.readBinFile file)
    let other ← findOLean (fixture `CoreSpec)
    for extension in ["olean", "olean.server", "olean.private", "ir", "ir.sig"] do
      if ← (other.withExtension extension).pathExists then
        IO.FS.writeBinFile (shadow.withExtension extension) (← IO.FS.readBinFile (other.withExtension extension))
    searchPathRef.set (dependency :: saved)
    unless (← findOLean challenge) == shadow do
      throwError "The dependency's {challenge} does not come first on the search path"
    let read ← Audit.readChallenge project challenge olean
    unless read.holes == #[challenge ++ `double] do
      throwError "The audit read a dependency's {challenge}, not the root package's: holes {read.holes}"
  finally
    searchPathRef.set saved
    IO.FS.removeDirAll dependency

run_cmd Elab.Command.liftTermElabM do
  let evidence := allEvidence (← getEnv)
  let world ← Audit.headline project evidence (fixture `successor_grows)
  let precondition ← Audit.headline project evidence (fixture `bounded)
  unless world.assumptions.map (·.claim) == #[fixture `SuccAgrees] do throwError "A world claim was misread"
  unless (evidence.filter (·.claim == fixture `SuccAgrees)).size == 3 && world.assumptions.map (·.checks) == #[2] do
    throwError "A Check of another instance of a claim counted"
  unless precondition.assumptions.isEmpty && precondition.unnamed.isEmpty do
    throwError "A precondition was read as an assumption"
  let missing ← try discard <| Audit.headline project evidence `SoftwareChallengeTests.Missing; pure false
    catch _ => pure true
  unless missing do throwError "A missing headline passed"
  let stated := (← getConstInfo (fixture `successor_grows)).type
  let unproved ← Audit.headline project evidence `SoftwareChallengeTests.Missing (some stated)
  unless !unproved.proved && unproved.assumptions.map (·.claim) == #[fixture `SuccAgrees] do
    throwError "A headline the solution does not state was not read from its Challenge statement"
  unless world.proved do throwError "A headline the solution states was reported unproved"
  let single ← Audit.headline project evidence (fixture `identity_three)
  let unnamed ← Audit.headline project evidence (fixture `uses_unnamed)
  unless single.oneInstance && unnamed.oneInstance && !world.oneInstance && !precondition.oneInstance do
    throwError "A headline was misread as quantifying over inputs, or as not"
  unless (Audit.describe toString single).endsWith "  (one instance)" &&
      !contains (Audit.describe toString world) "one instance" do
    throwError "The report misstated one instance: {Audit.describe toString single}"
  let bundles ← [(`bundled_three, 3), (`bundled_iff, 2), (`bundled_structure, 2), (`bundled_hidden, 2),
      (`not_bundled_exists, 1), (`identity_fixed, 1)].mapM fun (name, expected) => do
    return (name, expected, (← Audit.headline project evidence (fixture name)).laws)
  for (name, expected, found) in bundles do
    unless found == expected do throwError "{name} bundles {found} laws, expected {expected}"
  unless (Audit.describe toString (← Audit.headline project evidence (fixture `bundled_three))).endsWith
      "  (bundles 3 laws)" && !contains (Audit.describe toString world) "bundles" do
    throwError "The report misstated bundled laws"
  let ignored ← Audit.headline project evidence (fixture `successor_positive)
  let correct ← Audit.headline project evidence (fixture `successor_correct)
  unless ignored.assumptions.map (·.unused) == #[true] && correct.assumptions.map (·.unused) == #[false] &&
      world.assumptions.map (·.unused) == #[false] do
    throwError "The premise linter misread which proofs use their world claim"
  unless contains (Audit.describe toString ignored) "assumes SoftwareChallengeTests.Fixtures.SuccAgrees \
      (2 checks, unused by the proof)" && !contains (Audit.describe toString correct) "unused" do
    throwError "The report misstated an unused premise: {Audit.describe toString ignored}"
  let unlinted ← Audit.headline project evidence countdownTerminates
  unless unlinted.unlinted == some (fixture `Fixpoint) && world.unlinted.isNone do
    throwError "A headline proved without the premise linter was not found: {unlinted.unlinted}"
  expect (Audit.evidenced { headlines := #[unlinted, world] }) "countdown_terminates"
    "add `meta import SoftwareChallenge` to SoftwareChallengeTests.Fixtures.Fixpoint"
  if (Audit.evidenced { headlines := #[world] }).any (contains · "linter") then
    throwError "A headline proved with the premise linter was rejected"
  let headlines ← #[fixture `uses_unchecked, fixture `uses_live, fixture `uses_unnamed].mapM
    fun name => Audit.headline project evidence name
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
  if Audit.kills env replaceable (fixture `identity_fixed) (fixture `identity_fixed_rejects_bound) then
    throwError "A kill whose witness depends on a bound variable counted"
  unless Audit.kills env replaceable (fixture `identity_succ) (fixture `identity_succ_rejects_successor) do
    throwError "A kill whose statement carries metadata the headline's does not was not recognised"
  unless Audit.kills env replaceable (fixture `identity_twice) (fixture `identity_twice_rejects_marked) do
    throwError "A kill that carries metadata on one occurrence of its witness was not recognised"
  let foreign := (NameSet.empty.insert (fixture `successor)).insert (fixture `nativeSucc)
  unless Audit.kills env foreign (fixture `successor_correct) (fixture `successor_correct_rejects_identity) do
    throwError "A kill that replaces a foreign constant was not recognised"
  if Audit.kills env (NameSet.empty.insert (fixture `successor)) (fixture `successor_correct)
      (fixture `successor_correct_rejects_identity) then
    throwError "A kill that replaces a constant that is not replaceable counted"
  let statements := fun (names : Array Name) => names.mapM fun name => return (name, (← getConstInfo name).type)
  let restated : Audit.Challenge := {
    theorems := #[fixture `identity_fixed, fixture `identity_fixed_again, fixture `identity_three]
    statements := ← statements #[fixture `identity_fixed, fixture `identity_fixed_again, fixture `identity_three] }
  let repeated := Audit.meaningful { challenge := restated }
  expect repeated "identity_fixed_again states the same as SoftwareChallengeTests.Fixtures.identity_fixed;"
    "ask the owner to drop one from Challenge.lean"
  if repeated.any (contains · "identity_three states") then
    throwError "A headline with a different statement was reported as a duplicate: {repeated}"
  let order := #[fixture `identity_fixed, fixture `identity_twice]
  let independently := fixture `identity_fixed_rejects_independently
  unless Audit.independent env replaceable order (fixture `identity_fixed) independently do
    throwError "An independence kill was not recognised"
  if Audit.kills env replaceable (fixture `identity_fixed) independently then
    throwError "An independence kill was read as a plain kill"
  if Audit.independent env replaceable (order.push (fixture `identity_three)) (fixture `identity_fixed) independently then
    throwError "An independence kill missing a headline counted"
  if Audit.independent env replaceable order (fixture `identity_fixed) (fixture `identity_fixed_rejects_independently_mixed) then
    throwError "An independence kill with a different witness in one conjunct counted"
  if Audit.independent env replaceable #[fixture `identity_fixed] (fixture `identity_fixed)
      (fixture `identity_fixed_rejects_successor) then
    throwError "A plain kill of the only headline counted as independent"
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
  let terminatesType := (← getConstInfo countdownTerminates).type
  let fromStatement := Audit.terminations env #[(countdown, `SoftwareChallengeTests.Missing)]
    fun _ => some terminatesType
  unless fromStatement.all (·.mentioned) do
    throwError "A termination headline the solution does not state was not read from its statement"
  unless (termination countdown countdownTerminates).isEmpty do
    throwError "A listed termination headline was rejected: {termination countdown countdownTerminates}"
  expect (termination (fixture `Fixpoint.spin) countdownTerminates) "spin" "not a definition hole"
  expect (termination (fixture `Fixpoint.spin) countdownTerminates) "spin" "does not mention it"
  expect (termination (fixture `identity) (fixture `identity_fixed)) "identity" "not a partial_fixpoint definition"
  expect (termination countdown (fixture `Fixpoint.countdown_terminates_rejects_stuck)) "countdown"
    "not a headline with a kill"
  expect (termination countdown (fixture `bounded)) "countdown" "not a headline with a kill"
  expect (termination countdown (fixture `bounded)) "bounded" "does not mention it"
  let marked ← Audit.readChallenge project (fixture `Challenge) (← findOLean (fixture `Challenge))
  let member := fun (name : Name) => fixture (`Challenge ++ name)
  unless marked.theorems == #[member `double_even, member `double_even_rejects_identity,
      member `double_even_rejects_nothing, member `double_even_independent, member `double_even_partly_independent,
      member `double_even_independent_mixed, member `triple_rejects_nothing, member `double_zero, member `double_one,
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
  for kill in ["double_even_partly_independent", "double_even_independent_mixed"] do
    expect misread kill "nor that negation `∧` every other headline"
  if misread.any (contains · "double_even_independent:") then
    throwError "An independence kill was rejected: {misread}"
  unless marked.independent == #[member `double_even] do
    throwError "Independence was misread: {marked.independent}"
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

run_cmd Elab.Command.liftTermElabM do
  let member := fun (name : Name) => fixture (`WitnessChallenge ++ name)
  let read ← Audit.readChallenge project (fixture `WitnessChallenge) (← findOLean (fixture `WitnessChallenge))
  unless read.headlines == #[member `double_halves, member `double_positive, member `double_between,
      member `double_lengths, member `succ_hits_one, member `double_small, member `double_zero,
      member `double_negative_vanishes, member `double_nonnegative_vanishes, member `double_vanishes_only_at_zero,
      member `succ_law] do
    throwError "A witness was read as a headline: {read.headlines}"
  unless read.misshapenWitnesses.map (·.1) == #[member `double_positive_applies_unused,
      member `double_positive_applies_replaced, member `double_zero_applies, member `double_applies] do
    throwError "A witness was misjudged: {read.misshapenWitnesses}"
  let errors := Audit.meaningful { challenge := read }
  expect errors "double_halves: a precondition mentions SoftwareChallengeTests.Fixtures.WitnessChallenge.double"
    "state `∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n = 4` and mark it \
      `@[witness SoftwareChallengeTests.Fixtures.WitnessChallenge.double_halves]`"
  for witness in ["double_positive_applies_unused", "double_positive_applies_replaced"] do
    expect errors witness "but it is not `∃ n, 0 < SoftwareChallengeTests.Fixtures.WitnessChallenge.double n`"
  expect errors "double_zero_applies" "has no precondition to meet"
  expect errors "double_applies" "is not a headline of Challenge.lean"
  expect errors "double_negative_vanishes: a precondition mentions SoftwareChallengeTests.Fixtures.WitnessChallenge.double"
    "state `∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n < 0` and mark it"
  if errors.any fun error => ["double_small:", "double_positive:", "double_between:", "double_lengths:",
      "succ_hits_one:", "double_nonnegative_vanishes:", "double_vanishes_only_at_zero:", "succ_law:"].any fun headline => contains error headline && contains error "precondition" then
    throwError "A headline with a witness, or with preconditions the solution cannot change, was rejected: {errors}"
  unless contains (Audit.comparatorConfig `A.Solution read) (toString (member `double_positive_applies)) do
    throwError "A witness is missing from comparator.json"
  let pick := fixture `pick
  let some vacuous ← Audit.preconditionsOf project (NameSet.empty.insert pick) (fixture `pick_one_zero)
      (← getConstInfo (fixture `pick_one_zero)).type
    | throwError "The precondition of a vacuous headline was not read"
  let refuted := Audit.toShape (← getConstInfo (fixture `pick_one_zero_has_no_witness)).type
  unless vacuous.mentions == some pick &&
      refuted == (Shape.applicability vacuous.premises vacuous.inputs vacuous.preconditions).negation do
    throwError "The witness a vacuous headline needs is not the one its solution refutes"
  expect (Audit.meaningful { challenge := { theorems := #[fixture `pick_one_zero], preconditioned := #[vacuous] } })
    "pick_one_zero: a precondition mentions SoftwareChallengeTests.Fixtures.pick" "mark it `@[witness"
  let some negative := read.preconditioned.find? (·.headline == member `double_negative_vanishes)
    | throwError "The precondition a specification definition hides was not read"
  unless Audit.toShape (← getConstInfo ``double_negative_vanishes_has_no_witness).type ==
      (Shape.applicability negative.premises negative.inputs negative.preconditions).negation do
    throwError "The witness a hidden vacuous precondition needs is not the one its refutation rules out"
  if read.preconditioned.any (·.headline == member `double_vanishes_only_at_zero) then
    throwError "A world claim a headline concludes was unfolded into preconditions"
  let law ← Audit.headline project (allEvidence (← getEnv)) (member `double_negative_vanishes)
  let succLaw ← Audit.headline project (allEvidence (← getEnv)) (member `succ_law)
  let claimed ← Audit.headline project (allEvidence (← getEnv)) (member `double_vanishes_only_at_zero)
  unless !law.oneInstance && !succLaw.oneInstance && claimed.oneInstance do
    throwError "A headline stated as a specification definition was misread as one instance, or as not"
  unless succLaw.assumptions.map (·.claim) == #[fixture `SuccAgrees] do
    throwError "A world claim a specification definition assumes was not read: {succLaw.assumptions.map (·.claim)}"
  let pending : Audit.Headline := { name := `h, assumptions := #[], unnamed := #[], witnessProved := false }
  unless (Audit.describe toString pending).endsWith "  (witness not yet proved)" &&
      (Audit.describe toString { pending with proved := false }).endsWith "  (not yet proved)" do
    throwError "The report misstated an unproved witness: {Audit.describe toString pending}"
  let heavy ← Audit.headline project (allEvidence (← getEnv)) (fixture `succ_at_leaves)
  unless heavy.assumptions.map (·.checks) == #[0] do throwError "A Check that cannot be matched counted"
  expect (Audit.evidenced { headlines := #[heavy] }) "succ_at_leaves: cannot match Fixtures.SuccAt \
    (Fixtures.leafSum 30 1) against the Check at SoftwareChallengeTests.Fixtures.WorldCode, line 52" "budget"

run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let moduleOf := fun (name : Name) => (env.getModuleIdxFor? name).map (env.header.modules[·.toNat]!.module)
  let running := fun name => (moduleOf name).any valid.contains
  let program := { project with executable := true }
  let entry := fixture `loopIdentity
  let glue ← Audit.unclaimed program moduleOf running #[fixture `identity] entry
  unless glue == some (3, #[entry]) do throwError "Glue main runs was miscounted: {glue}"
  let covered ← Audit.unclaimed program moduleOf running #[entry] entry
  unless covered == some (3, #[]) do throwError "Code reached from a hole was counted unclaimed: {covered}"
  if (← Audit.unclaimed project moduleOf running #[] entry).isSome then
    throwError "A library without a lean_exe was reported unclaimed code"

end

end SoftwareChallengeTests.Audit

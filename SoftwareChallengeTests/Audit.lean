module

import all SoftwareChallengeTests.Fixtures.CoreSpec
import all SoftwareChallengeTests.Fixtures.WorldSpec
import all SoftwareChallengeTests.Fixtures.CoreCode
import all SoftwareChallengeTests.Fixtures.WorldCode
import all SoftwareChallengeTests.Fixtures.Sibling
import all SoftwareChallengeTests.Fixtures.Rejected
import all SoftwareChallengeTests.Fixtures.Fixpoint
import all SoftwareChallengeTests.Fixtures.Statements
import SoftwareChallengeTests.Fixtures.Challenge
import SoftwareChallengeTests.Fixtures.AuxiliaryChallenge
import SoftwareChallengeTests.Fixtures.WitnessChallenge
import all SoftwareChallengeTests.Fixtures.Twin
import all SoftwareChallengeTests.Fixtures.Draft
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

private def violations (project : Project) (inventory : Inventory) (challenge : Audit.Challenge := {}) :
    CoreM (Array String) := do
  return Audit.sound project { inventory, challenge, blames := ← Audit.blamesOf inventory }

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
    \"SoftwareChallengeTests.Fixtures.Challenge.double_even_rejects_itself\",
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

#guard
  let layout := Project.ofPackage #[`A.CoreSpec, `A.Helpers, `A.WorldSpec] false
  !layout.admits .coreSpec { name := `A.Helpers, comptime := true } &&
    !layout.admits .worldSpec { name := `A.Helpers, comptime := true } &&
    layout.admits .coreSpec { name := `Lean.Data.Name, comptime := true } &&
    layout.admits .worldSpec { name := `A.CoreSpec, comptime := true }

run_cmd Elab.Command.liftCoreM do
  let accepted ← Audit.collect valid
  unless project.check accepted do
    throwError "Valid fixtures were rejected:\n{← violations project accepted}"
  let reassign (module : Name) (role : Role) : Project :=
    { modules := project.modules.map fun (name, r) => (name, if name == module then role else r) }
  let rejected ← Audit.collect (valid.push (fixture `Rejected))
  for layout in #[project, reassign (fixture `Rejected) .coreSpec] do
    if layout.check rejected then throwError "Rejected fixtures passed"
    let found ← violations layout rejected
    for (name, reason) in #[("hiddenUnsafe", "unsafe"), ("diverging", "partial"),
        ("hiddenEffect", "IO"), ("packagedEffect", "IO"), ("startup", "runs IO when the program starts"),
        ("bound", "@[extern]"), ("Rejected.foreign", "@[extern]"), ("Rejected.replaced", "@[implemented_by]"),
        ("traced", "dbg builtin"), ("traceValue", "dbg builtin"), ("Rejected.raw", "asserts"),
        ("Rejected.viaRaw", "depends on axiom SoftwareChallengeTests.Fixtures.Rejected.raw"),
        ("Rejected.hole uses `sorry`", "Replace each `sorry` in SoftwareChallengeTests.Fixtures.Rejected.hole"),
        ("Rejected.decided is proved with `native_decide`", "with `decide`"),
        ("Fixtures.Rejected", "imports SoftwareChallengeTests.Fixtures.WorldSpec (WorldSpec), but"),
        ("Fixtures.Rejected", "Delete line 1, `import SoftwareChallengeTests.Fixtures.WorldSpec`")] do
      expect found name reason
    for (fragment, why) in [("_unsafe_rec", "A partial definition was reported by its compiler name"),
        ("_native", "A native_decide axiom was reported by its generated name"),
        ("_hyg", "An initializer was reported by its hygienic name"),
        ("chained", "A declaration that only uses an unproved one was reported, not the one it uses"),
        ("viaHole", "A declaration that is not a target was reported for using an unproved one"),
        ("or delete", "An unproved declaration was told to be deleted")] do
      if found.any (contains · fragment) then throwError "{why}: {found}"
  let target : Audit.Challenge := { declared := #[← getConstInfo (fixture `Rejected.viaHole)] }
  expect (← violations project rejected target) "Rejected.viaHole is not proved, because it uses \
    SoftwareChallengeTests.Fixtures.Rejected.hole" "whose proof uses `sorry`"
  for (module, role, facts, name, reason) in #[
      (fixture `CoreSpec, Role.coreCode, accepted, "Fixtures.WorldSpec", "may import only"),
      (fixture `WorldCode, .worldSpec, accepted, "Fixtures.WorldCode", "may import only"),
      (fixture `WorldCode, .worldSpec, accepted, "drain", "partial"),
      (fixture `CoreCode, .tooling, accepted, "Fixtures.WorldCode", "may import any module except tooling"),
      (fixture `CoreCode, .tooling, accepted, "Fixtures.WorldCode",
        "Rename SoftwareChallengeTests.Fixtures.CoreCode to a CoreCode or WorldCode module"),
      (fixture `Rejected, .worldCode, rejected, "hiddenUnsafe", "unsafe"),
      (fixture `Rejected, .worldCode, rejected, "bound", "@[extern]"),
      (fixture `Rejected, .worldCode, rejected, "Rejected.foreign", "@[extern]"),
      (fixture `Rejected, .worldCode, rejected, "Rejected.replaced", "@[implemented_by]"),
      (fixture `Rejected, .tooling, rejected, "Rejected.raw", "asserts"),
      (fixture `Rejected, .worldSpec, rejected, "bound", "@[extern] with a body the kernel unfolds"),
      (fixture `Rejected, .worldSpec, rejected, "hiddenEffect", "IO")] do
    expect (← violations (reassign module role) facts) name reason
  if (← violations (reassign (fixture `Rejected) .worldSpec) rejected).any (contains · "Rejected.foreign") then
    throwError "An @[extern] opaque declaration was rejected in a WorldSpec module"
  let fixpoints := valid.push (fixture `Fixpoint)
  let unproved ← Audit.collect fixpoints
  if project.check unproved then throwError "A partial_fixpoint without a termination headline passed"
  expect (← violations project unproved) "Fixpoint.countdown" "partial"
  let covered ← Audit.collect fixpoints (NameSet.empty.insert countdown)
  expect (← violations project covered) "Fixpoint.spin" "partial"
  if (← violations project covered).any (contains · "countdown") then
    throwError "A partial_fixpoint with a termination headline was reported partial"
  let listedPartial ← Audit.collect (valid.push (fixture `Rejected))
    (NameSet.empty.insert (fixture `Rejected.diverging))
  expect (← violations project listedPartial) "diverging" "partial"
  let legacy := { accepted with
    modules := accepted.modules.map ({ · with usesModuleSystem := false }) }
  if project.check legacy then throwError "A file without `module` passed"
  expect (← violations project legacy) "Fixtures.CoreCode" "does not start with `module`"
  let outside : Project := { modules := project.modules.filter (·.1 != fixture `WorldCode) }
  if outside.check accepted then throwError "A module outside the package was audited as one of it"
  expect (← violations outside accepted) "Fixtures.WorldCode" "no lean_lib of the package builds"
  let challenge := Audit.owned project {
    challengeImports := ← Audit.challengeImports "SoftwareChallengeTests/Fixtures/Challenge.lean" }
  expect challenge "Fixtures.CoreCode" "may import only CoreSpec and WorldSpec"
  if challenge.any (contains · "imports SoftwareChallenge,") then
    throwError "A challenge import from outside the package was rejected: {challenge}"
  let locked := #[("Challenge.lean", (1 : UInt64)), ("CoreSpec.lean", 2), ("Gone.lean", 3)]
  let drifted := Audit.lockErrors locked #[("Challenge.lean", 1), ("CoreSpec.lean", 5), ("New.lean", 4)]
    #["CoreCode.lean"] "Challenge.lean"
  expect drifted "CoreSpec.lean differs from owned.lock" "edit CoreCode.lean instead"
  expect drifted "CoreSpec.lean differs" "`git checkout $(git log -1 --format=%H -- owned.lock) -- CoreSpec.lean`"
  let configuration := Audit.lockErrors #[] #[("lean-toolchain", 1)] #[] "Challenge.lean"
  expect configuration "lean-toolchain is owned, because it fixes the Lean version" "Delete owned.lock and run"
  if configuration.any (contains · "Remove or rename") then
    throwError "An unrecorded configuration file was told to be removed: {configuration}"
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
  expect (Audit.pending { entry := some (some (fixture `WorldCode), #[`h]) }) "hole h" "is never called from main"
  if (Audit.pending { entry := some (some (fixture `WorldCode), #[`h]), standings := #[(`h, .absent)] }).any
      (contains · "never called from main") then
    throwError "A hole that is not implemented yet was also reported as never called from main"
  if !(Audit.sound project { entry := some (some (fixture `WorldCode), #[`h]) }).isEmpty then
    throwError "An unreached hole was reported as an error, not as pending"
  expect (Audit.sound project { entry := some (some (fixture `CoreCode), #[]) }) "main" "WorldCode module"
  let moduleOf := fun (_ : Name) => some (fixture `WorldCode)
  let missing := Audit.entryOf { project with executable := true } env moduleOf (fun _ => true) #[`h]
  unless missing matches some (none, #[]) do throwError "A missing main passed"
  expect (Audit.pending { entry := missing }) "main is not written yet" "declares a lean_exe"
  expect (Audit.pending { entry := missing, files := #[(`A.WorldCode, "A/WorldCode.lean")] })
    "A/WorldCode.lean: main is not written yet" "Add `def main : IO Unit := …` at the end of A/WorldCode.lean"
  if (Audit.entryOf project env moduleOf (fun _ => true) #[`h]).isSome then
    throwError "A library without a lean_exe was required to have a main"
  let registrations := (valid.push (fixture `Rejected)).flatMap fun module =>
    (PersistentEnvExtension.getModuleEntries claimsExt env (env.getModuleIdx? module).get!).map
      fun claim => (claim, module, project.role? module, (env.getModuleIdxFor? claim).map
        (env.header.modules[·.toNat]!.module))
  let registered := Audit.registered project { registrations }
  expect registered "CoreClaim" "only a WorldSpec module states"
  expect registered "Rejected adds SoftwareChallengeTests.Fixtures.Identity"
    "to the world claims without the `WorldClaim` command"
  if registered.any (contains · "WorldClaim SoftwareChallengeTests.Fixtures.Identity is declared") then
    throwError "A raw registration was reported as a WorldClaim declared where it is registered: {registered}"
  unless (← Audit.importLines "SoftwareChallengeTests/Fixtures/Challenge.lean").contains
      (fixture `CoreCode, 3, "public import SoftwareChallengeTests.Fixtures.CoreCode") do
    throwError "An import line was misread: {← Audit.importLines "SoftwareChallengeTests/Fixtures/Challenge.lean"}"
  if registered.any (contains · "SuccAgrees") then
    throwError "A claim declared in a WorldSpec module was rejected: {registered}"
  unless isNoncomputable env (fixture `lostHole) do throwError "A noncomputable definition was not found"
  expect (Audit.sound project {
      holes := #[(fixture `lostHole, some (fixture `CoreCode))]
      noncomputableHoles := #[fixture `lostHole] })
    "hole SoftwareChallengeTests.Fixtures.lostHole is `noncomputable`"
    "Define SoftwareChallengeTests.Fixtures.lostHole without `noncomputable`"
  let fixpointHole : Audit.Facts := { holes := #[(countdown, some (fixture `Fixpoint))], fixpoints := #[countdown] }
  expect (Audit.sound (reassign (fixture `Fixpoint) .worldCode) fixpointHole) "countdown is defined with \
    `partial_fixpoint`" "without `partial_fixpoint`"
  let terminated : Audit.Termination := {
    definition := countdown, headline := countdownTerminates, fixpoint := true, mentioned := true }
  if (Audit.sound (reassign (fixture `Fixpoint) .worldCode) { fixpointHole with terminations := #[terminated] }).any
      (contains · "is defined with `partial_fixpoint`") then
    throwError "A partial_fixpoint hole with a termination headline was rejected"
  let twins ← Audit.collect #[fixture `Twin, fixture `Draft]
  let twinIn := fun (module : Name) => twins.declarations.find? fun fact =>
    fact.name == fixture `twin_law && fact.moduleName == fixture module
  unless (twinIn `Draft).any (·.axioms.contains ``sorryAx) && (twinIn `Twin).any (·.axioms.isEmpty) do
    throwError "A sorry in a theorem another module also declares was not found"
  unless (← Audit.blamesOf twins).any fun blame => blame.declaration == fixture `twin_law && blame.axiomName == ``sorryAx do
    throwError "A sorry in a theorem another module also declares was not blamed"
  unless Audit.duplicatesIn env #[fixture `Twin, fixture `Draft] == #[(fixture `twin_law, fixture `Twin, fixture `Draft)] do
    throwError "A theorem two modules declare was not found: {Audit.duplicatesIn env #[fixture `Twin, fixture `Draft]}"
  expect (Audit.sound project {
      duplicates := #[(fixture `twin_law, fixture `Twin, fixture `Draft)]
      files := #[(fixture `Draft, "Draft.lean"), (fixture `Twin, "Twin.lean")] })
    "SoftwareChallengeTests.Fixtures.twin_law is declared in both" "Rename or delete SoftwareChallengeTests.Fixtures.twin_law \
      in Draft.lean"
  let program := Project.ofPackage #[`A.Main, `A.WorldCode] true
  expect (Audit.sound program {
      entry := some (some `A.Main, #[]), roots := #[`A.Main], files := #[(`A.Main, "A/Main.lean")] })
    "main is defined in A.Main (tooling), the root of the package's lean_exe"
    "set that lean_exe's `root` to a WorldCode module, such as A.WorldCode.Main"
  expect (Audit.pending { entry := some (none, #[]), roots := #[`A.Tool], files := #[(`A.WorldCode, "A/WorldCode.lean")] })
    "A.Tool is the root of the package's lean_exe, but no default target builds it" "mark that lean_exe `@[default_target]`"
  let specErrors := Audit.owned (Project.ofPackage #[`A.CoreSpec, `A.Notation] false) {
    files := #[(`A.CoreSpec, "A/CoreSpec.lean")]
    imports := #[(`A.CoreSpec, #[(`A.Notation, 3, "meta import A.Notation")])]
    specImports := #[(`A.CoreSpec, #[{ name := `A.Notation, comptime := true },
      { name := `Lean.Data.Name, comptime := true }])] }
  expect specErrors "A/CoreSpec.lean:3: A.CoreSpec (CoreSpec) meta-imports A.Notation (tooling)"
    "delete line 3, `meta import A.Notation`, from A/CoreSpec.lean; then delete owned.lock and run `lake build`"
  if specErrors.any (contains · "Lean.Data.Name") then throwError "A meta import from outside the package was rejected"
  unless (← Audit.headerImports "SoftwareChallengeTests/Fixtures/WorldSpec.lean").any
      fun found => found.name == `SoftwareChallenge && found.comptime do
    throwError "A meta import was misread"

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

private def moduleOf (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).map (env.header.modules[·.toNat]!.module)

private def analysed (evidence : Array Evidence) (name : Name) : MetaM Audit.Headline := do
  Audit.headline project evidence name (← getConstInfo name).type (moduleOf (← getEnv) name)

run_cmd Elab.Command.liftTermElabM do
  let evidence := allEvidence (← getEnv)
  let world ← analysed evidence (fixture `successor_grows)
  let precondition ← analysed evidence (fixture `bounded)
  unless world.assumptions.map (·.claim) == #[fixture `SuccAgrees] do throwError "A world claim was misread"
  unless (evidence.filter (·.claim == fixture `SuccAgrees)).size == 3 && world.assumptions.map (·.checks) == #[2] do
    throwError "A Check of another instance of a claim counted"
  unless precondition.assumptions.isEmpty && precondition.unnamed.isEmpty do
    throwError "A precondition was read as an assumption"
  let stated := (← getConstInfo (fixture `successor_grows)).type
  let unproved ← Audit.headline project evidence `SoftwareChallengeTests.Missing stated
  unless !unproved.proved && unproved.assumptions.map (·.claim) == #[fixture `SuccAgrees] do
    throwError "A headline the solution does not prove was not read from its Challenge statement"
  unless world.proved do throwError "A headline the solution proves was reported unproved"
  let unnamed ← analysed evidence (fixture `uses_unnamed)
  let hidden ← analysed evidence (fixture `hidden_succ)
  unless hidden.assumptions.map (·.claim) == #[fixture `SuccAgrees] && hidden.unnamed.isEmpty &&
      hidden.assumptions.map (·.checks) == world.assumptions.map (·.checks) do
    throwError "A world claim a WorldSpec definition wraps in a hypothesis was not read: \
      {hidden.assumptions.map (·.claim)} {hidden.unnamed}"
  let ignored ← analysed evidence (fixture `successor_positive)
  let correct ← analysed evidence (fixture `successor_correct)
  unless ignored.assumptions.map (·.unused) == #[true] && correct.assumptions.map (·.unused) == #[false] &&
      world.assumptions.map (·.unused) == #[false] do
    throwError "The premise linter misread which proofs use their world claim"
  unless contains (Audit.describe toString ignored) "assumes SoftwareChallengeTests.Fixtures.SuccAgrees \
      (2 checks, unused by the proof)" && !contains (Audit.describe toString correct) "unused" do
    throwError "The report misstated an unused premise: {Audit.describe toString ignored}"
  let everywhere ← analysed evidence (fixture `succ_everywhere)
  let positives ← analysed evidence (fixture `succ_on_positives)
  unless [everywhere, positives].all fun line => line.assumptions.map (·.claim) == #[fixture `SuccAt] &&
      line.assumptions.map (·.checks) == #[1] && line.unnamed.isEmpty do
    throwError "A world claim under ∀ or → was not read as an assumption with its Checks: \
      {everywhere.assumptions.map (·.checks)} {positives.assumptions.map (·.checks)} {everywhere.unnamed}"
  unless contains (Audit.describe toString positives) "assumes SoftwareChallengeTests.Fixtures.SuccAt (1 check)" do
    throwError "The report misstated a world claim under →: {Audit.describe toString positives}"
  let quantifiedIgnored ← analysed evidence (fixture `succ_everywhere_ignored)
  unless quantifiedIgnored.assumptions.map (·.unused) == #[true] && everywhere.assumptions.map (·.unused) == #[false] do
    throwError "The premise linter misread which proofs use a world claim under ∀"
  let quantifiedUnchecked ← #[fixture `unchecked_everywhere, fixture `unchecked_on_positives].mapM fun name =>
    analysed evidence name
  unless quantifiedUnchecked.all (·.assumptions.map (·.checks) == #[0]) do
    throwError "A Check of another claim counted for a world claim under ∀"
  let quantifiedPending := Audit.pending { headlines := quantifiedUnchecked }
  for name in ["unchecked_everywhere", "unchecked_on_positives"] do
    expect quantifiedPending name "UncheckedAt n := do …`, or `Check Fixtures.UncheckedAt n : <an instance it implies>`"
    expect quantifiedPending name "with a value of your choice in place of n"
  let some bounded ← Audit.preconditionsOf project {} (fixture `bounded_under_claim)
      (← getConstInfo (fixture `bounded_under_claim)).type
    | throwError "The precondition of a headline with a world claim under → was not read"
  unless bounded.premises.length == 1 && bounded.preconditions.length == 1 do
    throwError "A world claim under → was read as a precondition: {bounded.expected}"
  let unlinted ← analysed evidence countdownTerminates
  unless unlinted.unlinted == some (fixture `Fixpoint) && world.unlinted.isNone do
    throwError "A headline proved without the premise linter was not found: {unlinted.unlinted}"
  expect (Audit.evidenced { headlines := #[unlinted, world] }) "countdown_terminates"
    "Add `meta import SoftwareChallenge` to SoftwareChallengeTests.Fixtures.Fixpoint"
  if (Audit.evidenced { headlines := #[world] }).any (contains · "linter") then
    throwError "A headline proved with the premise linter was rejected"
  let headlines ← #[fixture `uses_unchecked, fixture `uses_live, fixture `uses_unnamed].mapM fun name => analysed evidence name
  let facts : Audit.Facts := {
    headlines := headlines.push world
    holes := #[(fixture `SuccAgrees, some (fixture `WorldSpec))]
    challenge := { hypotheses := #[(fixture `uses_unnamed, unnamed.unnamed)] } }
  let pending := Audit.pending facts
  expect pending "Unchecked" "which no Check tests"
  expect (Audit.sound project facts) "SuccAgrees" "defined in SoftwareChallengeTests.Fixtures.WorldSpec (WorldSpec)"
  expect (Audit.stated facts) "uses_unnamed" "which is not a WorldClaim"
  if pending.any (fun e => contains e "ClockAdvances" || contains e "SuccAgrees" && contains e "no Check") then
    throwError "Checks did not count: {pending}"
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
  expect repeated "identity_fixed_again states the same as SoftwareChallengeTests.Fixtures.identity_fixed"
    "Remove SoftwareChallengeTests.Fixtures.identity_fixed_again and its kills and witnesses from Challenge.lean"
  if repeated.any (contains · "identity_three states") then
    throwError "A headline with a different statement was reported as a duplicate: {repeated}"
  if repeated.any (contains · "identity_fixed_again has no kill") then
    throwError "A duplicate headline was also told to get a kill: {repeated}"
  expect (Audit.meaningful { challenge := { theorems := #[`F], fixed := #[`F] } }) "F mentions no hole or foreign \
    function" "State it about a hole"
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
  expect (Audit.meaningful { challenge := killed }) "bounded" "has no kill"
  expect (Audit.meaningful { challenge := { holes := #[`h] } }) "no headline mentions hole h" "or remove the hole"
  if (Audit.meaningful { challenge := killed }).any (contains · "identity_fixed") then
    throwError "A killed headline was reported unkilled"
  let stuck := fixture `Fixpoint.countdown_terminates_rejects_stuck
  let typeOf := fun (name : Name) => (env.find? name).map (·.type)
  let termination := fun (definition headline : Name) => Audit.stated {
    challenge := { theorems := #[countdownTerminates, stuck, fixture `bounded]
                   kills := #[(stuck, countdownTerminates)], holes := #[countdown, fixture `identity] }
    terminations := Audit.terminations (Audit.fixpoint env) #[(definition, headline)] typeOf }
  let fromStatement := Audit.terminations (Audit.fixpoint env) #[(countdown, `SoftwareChallengeTests.Missing)]
    fun _ => typeOf countdownTerminates
  unless fromStatement.all (·.mentioned) do
    throwError "A termination headline the solution does not state was not read from its statement"
  unless (termination countdown countdownTerminates).isEmpty do
    throwError "A listed termination headline was rejected: {termination countdown countdownTerminates}"
  expect (termination (fixture `Fixpoint.spin) countdownTerminates) "spin" "which is not a hole of"
  expect (termination (fixture `Fixpoint.spin) countdownTerminates) "spin" "does not mention"
  let implemented := fun (hole headline module : Name) => Audit.sound project {
    holes := #[(hole, some module)]
    terminations := Audit.terminations (Audit.fixpoint env) #[(hole, headline)] typeOf }
  expect (implemented (fixture `identity) (fixture `identity_fixed) (fixture `CoreCode)) "identity"
    "is not defined with `partial_fixpoint`"
  unless (implemented countdown countdownTerminates (fixture `Fixpoint)).isEmpty do
    throwError "A partial_fixpoint hole named by @[terminates] was rejected"
  expect (termination countdown (fixture `Fixpoint.countdown_terminates_rejects_stuck)) "countdown"
    "is not a headline with a kill"
  expect (termination countdown (fixture `bounded)) "countdown" "is not a headline with a kill"
  expect (termination countdown (fixture `bounded)) "bounded" "does not mention"
  let marked ← Audit.readChallenge project (fixture `Challenge) (← findOLean (fixture `Challenge))
  let member := fun (name : Name) => fixture (`Challenge ++ name)
  unless marked.theorems == #[member `double_even, member `double_even_rejects_identity,
      member `double_even_rejects_nothing, member `double_even_independent, member `double_even_partly_independent,
      member `double_even_independent_mixed, member `double_even_rejects_itself, member `triple_rejects_nothing,
      member `double_zero, member `double_one, member `double_one_rejects_one] &&
      marked.holes == #[member `double] && marked.filled == #[member `triple] &&
      marked.terminating == #[(member `triple, member `double_zero)] do
    throwError "The challenge was misread: {marked.theorems} {marked.holes} {marked.filled} {marked.terminating}"
  let markedFacts : Audit.Facts := {
    challenge := marked
    holes := marked.holes.map (·, some (fixture `CoreCode))
    terminations := Audit.terminations (Audit.fixpoint env) marked.terminating marked.statement? }
  let misread := Audit.meaningful markedFacts
  expect misread "double_zero" "has no kill"
  expect misread "double_one has no kill"
    "Mark SoftwareChallengeTests.Fixtures.Challenge.double_one_rejects_one `@[kills"
  if misread.any (contains · "double_one_rejects_one has no kill") then
    throwError "An unmarked kill was reported as a headline without a kill: {misread}"
  expect misread "double_even_rejects_nothing" "but it is neither `¬` SoftwareChallengeTests.Fixtures.Challenge.double_even"
  expect misread "triple_rejects_nothing" "is not a headline of Challenge.lean"
  expect misread "triple_rejects_nothing" "one of SoftwareChallengeTests.Fixtures.Challenge.double_even, "
  expect misread "double_even_rejects_itself is `¬` SoftwareChallengeTests.Fixtures.Challenge.double_even with no \
    hole replaced" "Replace SoftwareChallengeTests.Fixtures.Challenge.double in it"
  unless marked.fixed.isEmpty && (marked.templates.find? (·.1 == member `double_zero)).any
      (contains ·.2 "?wrong_double 0 = 0") do
    throwError "A kill template was misread: {marked.templates} {marked.fixed}"
  expect misread "double_zero has no kill" "?wrong_double 0 = 0"
  for kill in ["double_even_partly_independent", "double_even_independent_mixed"] do
    expect misread kill "nor that negation `∧` every other headline"
  if misread.any (contains · "double_even_independent is marked") then
    throwError "An independence kill was rejected: {misread}"
  unless marked.independent.map (·.1) == #[member `double_even] do
    throwError "Independence was misread: {marked.independent}"
  if misread.any fun error => contains error "double_even has no kill" ||
      contains error "double_even_rejects_identity is marked" then
    throwError "A marked kill was rejected: {misread}"
  expect (Audit.stated markedFacts) "triple" "which is not a hole of"
  let ownership := Audit.owned project markedFacts
  unless marked.axioms == #[member `double_axiom] && marked.privates.map (privateToUserName ·.1) == #[member `double_two] do
    throwError "An axiom or a private declaration of the challenge was misread: {marked.axioms} {marked.privates.map (·.1)}"
  expect ownership "SoftwareChallengeTests.Fixtures.Challenge.double_two is `private`" "Remove `private`"
  expect ownership "`axiom SoftwareChallengeTests.Fixtures.Challenge.double_axiom` asserts" "Delete \
    `axiom SoftwareChallengeTests.Fixtures.Challenge.double_axiom`"
  expect ownership "`deriving` makes SoftwareChallengeTests.Fixtures.instBEqForest.beq a `partial` definition in \
    SoftwareChallengeTests.Fixtures.CoreSpec (CoreSpec)" "then delete owned.lock and run `lake build`"
  if ownership.any (contains · "instBEqRose") then
    throwError "A derived partial instance in an editable module was reported to the owner: {ownership}"
  expect (Audit.owned project markedFacts) "defines SoftwareChallengeTests.Fixtures.Challenge.triple with a body"
    "Make SoftwareChallengeTests.Fixtures.Challenge.triple a hole with `:= sorry`"
  unless (Audit.solutionOf #[`A.CoreCode, `A.Solution]).toOption == some `A.Solution do
    throwError "The Solution module was not found"
  for (catalog, reason) in #[(#[`A.CoreCode], "builds no module named Solution"),
      (#[`A.Solution, `B.Solution], "Rename all but the module that proves")] do
    let .error error := Audit.solutionOf catalog | throwError "{catalog} named one Solution module"
    unless contains error reason do throwError "A Solution error was unclear: {error}"
  let generated := Audit.comparatorConfig `A.Solution marked
  unless generated == expectedConfig do throwError "Generated comparator.json:\n{generated}"

run_cmd Elab.Command.liftTermElabM do
  let member := fun (name : Name) => fixture (`WitnessChallenge ++ name)
  let read ← Audit.readChallenge project (fixture `WitnessChallenge) (← findOLean (fixture `WitnessChallenge))
  unless read.headlines == #[member `double_halves, member `double_positive, member `double_between,
      member `double_lengths, member `succ_hits_one, member `double_small, member `double_zero,
      member `double_negative_vanishes, member `double_nonnegative_vanishes, member `double_vanishes_only_at_zero,
      member `double_zero_fin, member `double_fin, member `double_positive_one, member `double_kept,
      member `double_kept_plain, member `succ_law] do
    throwError "A witness was read as a headline: {read.headlines}"
  unless read.misshapenWitnesses.map (·.1) == #[member `double_positive_applies_unused,
      member `double_positive_applies_replaced, member `double_zero_applies, member `double_kept_applies_lossy,
      member `double_kept_plain_applies_lossy, member `double_applies] do
    throwError "A witness was misjudged: {read.misshapenWitnesses}"
  let errors := Audit.meaningful { challenge := read }
  expect errors "a precondition of SoftwareChallengeTests.Fixtures.WitnessChallenge.double_halves mentions \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double"
    "Add `@[witness SoftwareChallengeTests.Fixtures.WitnessChallenge.double_halves] theorem double_halves_applies : \
      ∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n = 4 := by sorry`"
  for witness in ["double_positive_applies_unused", "double_positive_applies_replaced"] do
    expect errors witness "but it is not `∃ n, 0 < SoftwareChallengeTests.Fixtures.WitnessChallenge.double n`"
  expect errors "the type of an input of SoftwareChallengeTests.Fixtures.WitnessChallenge.double_fin mentions \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double" "theorem double_fin_applies : ∃ i, True := by sorry"
  if errors.any (contains · "double_positive_one_applies") then
    throwError "A hypothesis about a hole that mentions no input was told to get a witness: {errors}"
  let hypotheses := Audit.stated { challenge := read }
  expect hypotheses "double_positive_one assumes `0 < SoftwareChallengeTests.Fixtures.WitnessChallenge.double 1`, which \
    is about hole SoftwareChallengeTests.Fixtures.WitnessChallenge.double" "Remove the hypothesis, or state it as its \
    own headline"
  if hypotheses.any (contains · "which is not a WorldClaim") then
    throwError "A hypothesis about a hole was told to become a WorldClaim: {hypotheses}"
  expect errors "double_zero_applies" "has no precondition to meet"
  expect errors "double_applies" "is not a headline of Challenge.lean"
  expect errors "a precondition of SoftwareChallengeTests.Fixtures.WitnessChallenge.double_negative_vanishes \
      mentions SoftwareChallengeTests.Fixtures.WitnessChallenge.double"
    "∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n < 0 := by sorry`"
  if errors.any fun error => ["double_small", "double_positive", "double_between", "double_lengths",
      "succ_hits_one", "double_nonnegative_vanishes", "double_vanishes_only_at_zero", "succ_law"].any fun headline =>
        contains error s!"a precondition of {member headline.toName} mentions" then
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
    "a precondition of SoftwareChallengeTests.Fixtures.pick_one_zero mentions SoftwareChallengeTests.Fixtures.pick"
    "`@[witness SoftwareChallengeTests.Fixtures.pick_one_zero] theorem pick_one_zero_applies"
  let some negative := read.preconditioned.find? (·.headline == member `double_negative_vanishes)
    | throwError "The precondition a specification definition hides was not read"
  unless Audit.toShape (← getConstInfo ``double_negative_vanishes_has_no_witness).type ==
      (Shape.applicability negative.premises negative.inputs negative.preconditions).negation do
    throwError "The witness a hidden vacuous precondition needs is not the one its refutation rules out"
  if read.preconditioned.any (·.headline == member `double_vanishes_only_at_zero) then
    throwError "A world claim a headline concludes was unfolded into preconditions"
  let evidence := allEvidence (← getEnv)
  let succLaw ← analysed evidence (member `succ_law)
  unless succLaw.assumptions.map (·.claim) == #[fixture `SuccAgrees] do
    throwError "A world claim a specification definition assumes was not read: {succLaw.assumptions.map (·.claim)}"
  let line : Audit.Headline := { name := `h, assumptions := #[], unnamed := #[] }
  for (shown, ending) in [({ line with witnessProved := false }, "h  (witness not yet proved)"),
      ({ line with killProved := false }, "h  (kill not yet proved)"),
      ({ line with proved := false }, "h  (not yet proved)"),
      ({ line with proved := false, marker := "stated differently", killProved := false },
        "h  (stated differently)  (kill not yet proved)")] do
    unless Audit.describe toString shown == ending do
      throwError "The report misstated what is pending: {Audit.describe toString shown}, expected {ending}"
  let heavy ← analysed evidence (fixture `succ_at_leaves)
  unless heavy.assumptions.map (·.checks) == #[0] do throwError "A Check that cannot be matched counted"
  expect (Audit.pending { headlines := #[heavy] }) "SoftwareChallengeTests.Fixtures.WorldCode:52: this Check cannot \
    be matched against Fixtures.SuccAt (Fixtures.leafSum 30 1)" "budget"

private def renamed (info : ConstantInfo) (name : Name) : ConstantInfo :=
  match info with
  | .thmInfo value => .thmInfo { value with name }
  | .defnInfo value => .defnInfo { value with name }
  | .opaqueInfo value => .opaqueInfo { value with name }
  | .axiomInfo value => .axiomInfo { value with name }
  | other => other

private def tag : Audit.Standing → String
  | .holds _ => "holds"
  | .unsound _ => "unsound"
  | .absent => "absent"
  | .outside _ => "outside"
  | .kind _ _ => "kind"
  | .universes _ _ => "universes"
  | .differs _ _ _ => "differs"
  | .auxiliary _ _ => "auxiliary"

run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let statement := fun (name : Name) => fixture (`Statements ++ name)
  let imports := NameSet.empty.insert (fixture `Statements)
  let standingOf := fun (stated found : Name) (auxiliaries : Array ConstantInfo) (closure : NameSet) => do
    Audit.standing env (moduleOf env) closure auxiliaries (renamed (← getConstInfo (statement stated)) (statement found))
  for (stated, found, expected) in [(`zero_right, `zero_right_renamed, "holds"),
      (`zero_right, `zero_right_implicit, "holds"), (`zero_right, `zero_right_strict, "holds"),
      (`zero_right, `zero_right_marked, "holds"), (`hole, `hole_abbrev, "holds"), (`in_u, `in_u, "holds"),
      (`zero_right, `zero_right_assuming, "differs"), (`zero_right, `zero_right_flipped, "differs"),
      (`add_swap, `add_swap_reordered, "differs"), (`twice_eq, `twice_eq_unfolded, "differs"),
      (`twice_twice, `twice_twice_composed, "differs"), (`hole, `hole_optional, "differs"),
      (`in_u, `in_v, "universes"), (`in_uv, `in_vu, "universes"), (`in_u, `in_one, "universes"),
      (`zero_right, `zero_right_def, "kind"), (`hole, `hole_opaque, "kind"), (`hole, `hole_partial, "kind"),
      (`hole, `hole_unsafe, "kind")] do
    let judged ← tag <$> standingOf stated found #[] imports
    unless judged == expected do throwError "{found} restating {stated} was judged {judged}, expected {expected}"
  let one ← getConstInfo (statement `aux_one)
  unless tag (← standingOf `zero_right `zero_right_renamed #[one] imports) == "holds" &&
      tag (← standingOf `zero_right `zero_right_renamed #[renamed (← getConstInfo (statement `aux_two)) one.name]
        imports) == "auxiliary" &&
      tag (← standingOf `zero_right `zero_right_renamed #[] {}) == "outside" &&
      tag (← Audit.standing env (moduleOf env) imports #[] (renamed one `SoftwareChallengeTests.Missing)) == "absent" do
    throwError "An auxiliary constant, the Solution's imports, or a missing constant was misjudged"
  let challenge : Audit.Challenge := {
    theorems := #[`T, `K], holes := #[`H], kills := #[(`K, `T)], lines := #[(`T, 3), (`K, 5), (`H, 1)]
    signatures := #[(`T, "(n : Nat) : n + 0 = n"), (`K, ": ¬ ∀ n : Nat, n = n + 1"), (`H, ": Nat → Nat")]
    rendered := #[(`T, ("∀ (n : Nat), n + 0 = n", "∀ (n : Nat), @Eq Nat (n + 0) n"))] }
  let facts : Audit.Facts := {
    challenge, solution := `A.Solution, files := #[(`A.Solution, "A/Solution.lean"), (`A.Proofs, "A/Proofs.lean")]
    standings := #[(`T, .absent), (`H, .absent), (`K, .absent)] }
  let pending := Audit.pending facts
  expect pending "Challenge.lean:3: T is not proved yet"
    "Add `theorem T (n : Nat) : n + 0 = n := …`, with a proof, to A/Solution.lean, then run `lake lint`"
  expect pending "Challenge.lean:1: hole H is not implemented yet" "Add `def H : Nat → Nat := …` to a CoreCode module"
  expect pending "Challenge.lean:5: K is not proved yet" "so nothing shows that T rejects a wrong implementation"
  let moved := Audit.pending { facts with standings := #[(`T, .outside `A.Proofs)] }
  expect moved "A/Proofs.lean: T is in A.Proofs, which A.Solution does not import"
    "Add `public import A.Proofs` to the imports of A/Solution.lean"
  expect (Audit.pending { facts with standings := #[(`T, .outside `A.Proofs)], cyclic := #[`A.Proofs] })
    "A/Proofs.lean: T is in A.Proofs, which imports A.Solution, so A.Solution cannot import it back"
    "Move `theorem T` from A/Proofs.lean into A/Solution.lean"
  unless (Audit.pending { facts with standings := #[(`T, .unsound `A.Solution)] }).isEmpty do
    throwError "A target whose proof uses an unproved declaration was listed as pending, not as an error"
  let flipped := Audit.pending { facts with standings := #[(`T, .differs `A.Solution "∀ (n : Nat), n = n + 0" "")] }
  expect flipped "T states `∀ (n : Nat), n = n + 0` in A.Solution, but `∀ (n : Nat), n + 0 = n` in Challenge.lean:3"
    "Restate it as `theorem T (n : Nat) : n + 0 = n := …`"
  let alike := Audit.pending { facts with
    standings := #[(`T, .differs `A.Solution "∀ (n : Nat), n + 0 = n" "∀ (n : Nat), @Eq.{1} Nat (n + 0) n")] }
  expect alike "states `∀ (n : Nat), @Eq.{1} Nat (n + 0) n`" "but `∀ (n : Nat), @Eq Nat (n + 0) n` in Challenge.lean:3"
  let config := Audit.comparatorConfig `A.Solution challenge
  unless (Audit.comparatorErrors config (some config) false).isEmpty do
    throwError "A current comparator.json was rejected"
  expect (Audit.comparatorErrors config none false) "lakefile.lean has no `statement` target"
    Audit.statementTarget
  expect (Audit.comparatorErrors config none true) "comparator.json is missing" "Run `lake build`"
  let stale := Audit.comparatorConfig `B.Solution { challenge with theorems := #[`T, `Old] }
  for reason in ["it lists Old, which Challenge.lean no longer declares", "it omits K, which Challenge.lean declares",
      "it names the solution module \"B.Solution\", but the package's is \"A.Solution\""] do
    expect (Audit.comparatorErrors config (some stale) true) "comparator.json does not match Challenge.lean" reason
  let auxiliary ← Audit.readChallenge project (fixture `AuxiliaryChallenge) (← findOLean (fixture `AuxiliaryChallenge))
  expect (Audit.stated { challenge := auxiliary }) "first_is_zero" "elaborates to the private constant"
  if (Audit.meaningful { challenge := auxiliary }).any (contains · "first_is_zero has no kill") then
    throwError "A headline whose statement no solution can reproduce was also told to get a kill"
  unless auxiliary.fixed == #[fixture `AuxiliaryChallenge.first_is_zero] do
    throwError "A headline that mentions no hole was not found: {auxiliary.fixed}"
  let source := "theorem foo (n : Nat) :\n    n = n := by\n  sorry\ntheorem bar (x : Nat := 0) : x = x := rfl\n"
  unless Audit.signatureAt source ⟨1, 11⟩ == some "(n : Nat) : n = n" &&
      Audit.signatureAt source ⟨4, 11⟩ == some "(x : Nat := 0) : x = x" do
    throwError "A signature was misread: {Audit.signatureAt source ⟨1, 11⟩} {Audit.signatureAt source ⟨4, 11⟩}"
  let signed ← Audit.readChallenge project (fixture `Challenge) (← findOLean (fixture `Challenge))
    (← IO.FS.readFile "SoftwareChallengeTests/Fixtures/Challenge.lean")
  unless signed.signatureOf (fixture `Challenge.double_even) == "theorem double_even (n : Nat) : double n % 2 = 0" &&
      signed.signatureOf (fixture `Challenge.double) == "def double : Nat → Nat" &&
      signed.namespaceOf (fixture `Challenge.double_even) == fixture `Challenge do
    throwError "A Challenge signature was misread: {signed.signatureOf (fixture `Challenge.double_even)}"

end

end SoftwareChallengeTests.Audit

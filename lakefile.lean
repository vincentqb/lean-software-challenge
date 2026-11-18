import Lake
open Lean Lake DSL

package «software_challenge» where
  builtinLint := true
  fixedToolchain := true
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩,
    ⟨`linter.coreInternal, false⟩
  ]

@[default_target]
lean_lib «SoftwareChallenge» where
  globs := #[.andSubmodules `SoftwareChallenge]

lean_lib «SoftwareChallengeTests» where
  precompileModules := true
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]

def challengeMissing : String :=
  "the package has no module Challenge, which states the challenge. Create Challenge.lean and add \
    `lean_lib «Challenge» where leanOptions := #[⟨`warn.sorry, false⟩]` to lakefile.lean, then run `lake build`."

def auditMissing : String :=
  "SoftwareChallenge.Audit is not in the workspace, so the audit cannot run. Add `require software_challenge from \
    git \"https://github.com/vincentqb/lean-software-challenge\" @ \"main\"` to lakefile.lean, run \
    `lake update software_challenge`, then run `lake build`."

def packageModules (pkg : Package) (challenge : Lake.Module) : FetchM (Array Lake.Module) := do
  let mut modules := #[]
  for root in (← (← pkg.defaultModules.fetch).await).push challenge do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || mod.name == challenge.name || modules.any (·.name == mod.name) do
        modules := modules.push mod
  return modules

def sandboxCovers : Array System.FilePath := #["/home", "/root", "/run", "/tmp", "/var"]

def within (dir root : System.FilePath) : Bool :=
  root.components.isPrefixOf dir.components

def hiddenFromSandbox (workspace : Workspace) (root : Package) : IO (Array (Name × System.FilePath)) := do
  let rootDir ← IO.FS.realPath root.dir
  let mut hidden := #[]
  for pkg in workspace.packages do
    let dir ← IO.FS.realPath pkg.dir
    unless within dir rootDir || !sandboxCovers.any (within dir ·) do
      hidden := hidden.push (pkg.baseName, dir)
  return hidden

def auditOutput (pkg : Package) (mode : String) (flags : Array String) (challenge : Lake.Module)
    (olean : System.FilePath) (catalog : Array Lake.Module) : JobM IO.Process.Output := do
  IO.Process.output {
    cmd := (← getLean).toString
    args := #["--run", (__dir__ / "Audit.lean").toString, mode] ++ flags ++
      (if pkg.leanExes.isEmpty then #[] else #["--executable"]) ++
      #[challenge.relLeanFile.toString, olean.toString] ++
      catalog.map fun mod => s!"{mod.name}={mod.relLeanFile}"
    cwd := some pkg.dir
    env := ← getAugmentedEnv
  }

def addFileTraces (pkg : Package) (files : List String) : JobM Unit := do
  addTrace (← BuildTrace.compute (TextFilePath.mk (__dir__ / "Audit.lean")))
  for file in files do
    if ← (pkg.dir / file).pathExists then addTrace (← BuildTrace.compute (TextFilePath.mk (pkg.dir / file)))

package_facet softwareChallengeStatement pkg : Unit := do
  let some audit ← findModule? `SoftwareChallenge.Audit | error auditMissing
  let some challenge := pkg.findModule? `Challenge | error challengeMissing
  let catalog ← packageModules pkg challenge
  let mut job := Job.nil.mix (← audit.leanArts.fetch)
  for mod in ← (← challenge.transImports.fetch).await do
    if mod.pkg.keyName == pkg.keyName then job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do
    addFileTraces pkg ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "owned.lock"]
    addPureTrace (" ".intercalate (catalog.map fun mod => s!"{mod.name}={mod.relLeanFile}").toList) "modules"
    for mod in catalog.push challenge do
      if mod.name == challenge.name ||
          mod.name.components.any fun part => part.toString == "CoreSpec" || part.toString == "WorldSpec" then
        addTrace (← BuildTrace.compute (TextFilePath.mk mod.leanFile))
    let report := pkg.buildDir / "softwareChallengeStatement.txt"
    let written := pkg.buildDir / "comparator.json"
    let current ← if ← (pkg.dir / "comparator.json").pathExists then
      some <$> IO.FS.readFile (pkg.dir / "comparator.json") else pure none
    let previous ← if ← written.pathExists then some <$> IO.FS.readFile written else pure none
    unless current.isSome && current == previous do
      if ← (report.addExtension "trace").pathExists then IO.FS.removeFile (report.addExtension "trace")
    buildUnlessUpToDate report (← getTrace) (report.addExtension "trace") do
      let olean := pkg.buildDir / "softwareChallenge" / "statement" / "Challenge.olean"
      IO.FS.createDirAll (pkg.buildDir / "softwareChallenge" / "statement")
      let compiled ← IO.Process.output {
        cmd := (← getLean).toString
        args := #[challenge.leanFile.toString, "-o", olean.toString] ++ challenge.leanOptions.values.foldl
          (fun args name value => args.push s!"-D{name}={value.asCliFlagValue}") #[]
        cwd := some pkg.dir
        env := ← getAugmentedEnv
      }
      unless compiled.exitCode == 0 do
        logError (compiled.stdout ++ compiled.stderr)
        error s!"{challenge.relLeanFile} does not compile, so its statements cannot be checked: fix the errors \
          above, then run `lake build`."
      let out ← auditOutput pkg "statement" #[] challenge olean catalog
      unless out.exitCode == 0 do
        logError (out.stdout ++ out.stderr)
        error "the statement check failed: fix each error above as it says, then run `lake build`."
      IO.FS.writeFile report out.stdout
      if ← (pkg.dir / "comparator.json").pathExists then
        IO.FS.writeFile written (← IO.FS.readFile (pkg.dir / "comparator.json"))
      unless out.stdout.isEmpty do logInfo out.stdout

package_facet softwareChallenge pkg : Unit := do
  let some audit ← findModule? `SoftwareChallenge.Audit | error auditMissing
  let some challenge := pkg.findModule? `Challenge | error challengeMissing
  let catalog ← packageModules pkg challenge
  for mod in catalog do
    if (← (← mod.imports.fetch).await).any (·.name == challenge.name) then
      error s!"{mod.relLeanFile}: {mod.name} imports {challenge.name}, but the comparator checks the solution \
        against {challenge.name}, whose holes the solution redefines. Replace `import {challenge.name}` in \
        {mod.relLeanFile} with the CoreSpec and WorldSpec modules it needs, then run `lake lint`."
  let hidden ← hiddenFromSandbox (← getWorkspace) pkg
  let flags := (if pkg.defaultTargets.contains `statement then #["--target"] else #[]) ++
    hidden.map fun (name, dir) => s!"--hidden={name}={dir}"
  let mut job := (Job.nil.mix (← audit.leanArts.fetch)).mix (← challenge.leanArts.fetch)
  for mod in catalog do
    job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do
    addFileTraces pkg ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "owned.lock", "comparator.json"]
    addPureTrace (" ".intercalate flags.toList) "flags"
    let report := pkg.buildDir / "softwareChallenge.txt"
    buildUnlessUpToDate report (← getTrace) (report.addExtension "trace") do
      let out ← auditOutput pkg "solution" flags challenge challenge.oleanFile catalog
      unless out.exitCode == 0 || out.exitCode == 2 do
        logError (out.stdout ++ out.stderr)
        error "the audit found errors: fix each error above as it says, then run `lake lint`."
      IO.FS.writeFile report out.stdout
      logInfo ("\n" ++ out.stdout)

def statementTarget : String :=
  "@[default_target]\ntarget statement pkg : Unit := do\n  \
    return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())"

def pendingCount (report : String) : Nat :=
  ((report.splitOn "\n").findSome? fun line => (line.dropPrefix? "Pending: ").bind (·.toString.toNat?)).getD 0

def auditSolution (pkg : Package) : ScriptM UInt32 := do
  try
    discard <| runBuild (pkg.fetchFacetJob `softwareChallenge)
  catch _ =>
    return 1
  return if pendingCount (← IO.FS.readFile (pkg.buildDir / "softwareChallenge.txt")) == 0 then 0 else 2

script lint_challenge do
  let pkg ← getRootPackage
  let code ← auditSolution pkg
  unless pkg.config.builtinLint? == some true do
    IO.eprintln "lakefile.lean does not set `builtinLint := true`, so `lake lint` did not run Lean's linters. Add \
      `builtinLint := true` to the `package` block of lakefile.lean, then run `lake lint`."
    return 1
  if code == 2 then
    let count := pendingCount (← IO.FS.readFile (pkg.buildDir / "softwareChallenge.txt"))
    IO.eprintln s!"lake lint found no errors, but {count} {if count == 1 then "item is" else "items are"} pending, \
      as listed under Pending above, so the solution is not complete. Do each as it says, then run `lake lint`."
  return code

def runChecks (lake : String) (pkg : Package) : ScriptM UInt32 := do
  let some challenge := pkg.findModule? `Challenge | do IO.eprintln challengeMissing; return 1
  let modules ← runBuild do return Job.pure (← packageModules pkg challenge)
  let runner := pkg.buildDir / "softwareChallenge" / "Checks.lean"
  IO.FS.createDirAll (pkg.buildDir / "softwareChallenge")
  IO.FS.writeFile runner <| "\n".intercalate <| ["import SoftwareChallenge"] ++
    (modules.map (s!"import {·.name}")).toList ++
    [s!"run_cmd SoftwareChallenge.runChecks #[{", ".intercalate (modules.map fun mod =>
      s!"(`{mod.name}, {(toJson mod.relLeanFile.toString).compress})").toList}]", ""]
  (← IO.Process.spawn { cmd := lake, args := #["lean", runner.toString], cwd := pkg.dir }).wait

script run_checks do
  runChecks (← getLake).toString (← getRootPackage)

def ownTests (pkg : Package) (names : List String) : ScriptM UInt32 := do
  let mut worst := 0
  for name in names do
    match pkg.scripts.find? name.toName with
    | some found => worst := max worst (← found.run [])
    | none =>
      IO.eprintln s!"testDriverArgs in lakefile.lean names {name}, but lakefile.lean declares no script {name}, so \
        it cannot run. Declare `script {name} do …` in lakefile.lean, or remove \"{name}\" from testDriverArgs, \
        then run `lake test`."
      worst := max worst 1
  return worst

script test_challenge (args) do
  let pkg ← getRootPackage
  let checks ← runChecks (← getLake).toString pkg
  return max checks (← ownTests pkg args)

def tenths (ms : Nat) : String := s!"{ms / 1000}.{ms % 1000 / 100} s"

def replayEach (lake : String) (dir buildDir : System.FilePath) : IO UInt32 := do
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (dir / "comparator.json"))
  let theorems ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let configs := buildDir / "softwareChallenge" / "comparator"
  IO.FS.createDirAll configs
  let next ← IO.mkRef 0
  let results ← IO.mkRef (#[] : Array (String × IO.Process.Output × Nat))
  let worker : IO Unit := do
    repeat
      let index ← next.modifyGet fun index => (index, index + 1)
      let some name := theorems[index]? | break
      let file := configs / s!"{index}.json"
      IO.FS.writeFile file (config.setObjVal! "theorem_names" (toJson #[name])).pretty
      let start ← IO.monoMsNow
      let replay : IO IO.Process.Output :=
        IO.Process.output { cmd := lake, args := #["comparator", "--config", file.toString], cwd := dir }
      let mut output ← replay
      for _ in [0:3] do
        unless (output.stdout ++ output.stderr).contains "bwrap: Can't bind mount" do break
        IO.sleep 20000
        output ← replay
      let elapsed := (← IO.monoMsNow) - start
      results.modify (·.push (name, output, elapsed))
  let start ← IO.monoMsNow
  let threads := min 16 (System.Platform.Internal.getHardwareConcurrency ()).toNat
  let jobs := ((← IO.getEnv "SOFTWARE_CHALLENGE_JOBS").bind (·.toNat?)).getD threads
  let slots := min theorems.size (max 1 jobs)
  let workers ← (List.range slots).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for task in workers do IO.ofExcept task.get
  let total := (← IO.monoMsNow) - start
  let done := (← results.get).qsort fun a b => a.2.2 > b.2.2
  for (name, output, _) in done do
    unless output.exitCode == 0 do
      IO.eprintln s!"`lake comparator` {if output.exitCode == 1 then "rejects" else "could not check"} {name}:\n\
        {output.stdout}{output.stderr}\nFix what it reports, then run `lake script run software_challenge/replay`."
  let lines := done.map fun (name, output, elapsed) =>
    if output.exitCode == 0 then s!"{name}  {tenths elapsed}"
    else if output.exitCode == 1 then s!"{name}  {tenths elapsed}  (rejected)"
    else s!"{name}  {tenths elapsed}  (could not run, exit {output.exitCode})"
  let accepted := (done.filter (·.2.1.exitCode == 0)).size
  let report := "\n".intercalate (lines.push s!"Replayed: {accepted} of {theorems.size} theorems in {tenths total}").toList
  IO.FS.writeFile (buildDir / "comparator.txt") (report ++ "\n")
  IO.println report
  if done.any (·.2.1.exitCode == 1) then return 1
  if done.any (·.2.1.exitCode != 0) then return 2
  return 0

script replay do
  let pkg ← getRootPackage
  unless ← (pkg.dir / "comparator.json").pathExists do
    IO.eprintln "comparator.json is missing: `lake build` writes it from Challenge.lean, and replay reads it. Run \
      `lake build`, then run `lake script run software_challenge/replay`."
    return 1
  replayEach (← getLake).toString pkg.dir pkg.buildDir

script grade_candidate (args) do
  let lake := (← getLake).toString
  let pkg ← getRootPackage
  let commit := args.headD "the candidate"
  let again := s!"then run `lake exe grade {commit}` from the base checkout"
  let hidden ← hiddenFromSandbox (← getWorkspace) pkg
  for (name, dir) in hidden do
    IO.eprintln s!"cannot judge: the comparator's sandbox hides package {name} at {dir}, because it mounts empty \
      directories over /home, /root, /run, /tmp, and /var, so `lake comparator` cannot build {commit}. In \
      lakefile.lean, require {name} from git, or from a directory outside those, commit it, {again}."
  unless hidden.isEmpty do return 3
  let refuse (step : String) : ScriptM UInt32 := do
    IO.eprintln s!"refused: `{step}` fails on {commit}, as printed above. Fix what it reports in {commit}, {again}."
    return 1
  for (args, step) in [(#["build"], "lake build"), (#["lint", "--builtin-only"], "lake lint --builtin-only")] do
    unless (← (← IO.Process.spawn { cmd := lake, args, cwd := pkg.dir }).wait) == 0 do return ← refuse step
  match ← auditSolution pkg with
  | 0 => pure ()
  | 2 =>
    IO.eprintln s!"refused: {commit} is not complete: the audit lists pending items above. Finish them in \
      {commit}, {again}."
    return 1
  | _ => return ← refuse "lake lint"
  unless (← runChecks lake pkg) == 0 do return ← refuse "lake script run software_challenge/run_checks"
  let own ← if pkg.testDriver == "software_challenge/test_challenge" then ownTests pkg pkg.testDriverArgs.toList
    else if pkg.testDriver.isEmpty then pure 0
    else (← IO.Process.spawn { cmd := lake, args := #["test"], cwd := pkg.dir }).wait
  unless own == 0 do return ← refuse "lake test"
  return 0

lean_exe «grade» where
  root := `SoftwareChallenge.Grade

def replayTimes (report : String) : Array (String × Nat) :=
  (report.splitOn "\n").toArray.filterMap fun line =>
    match (line.splitOn "  ", line.splitOn " in ") with
    | ([name, time], _) | (_, [name, time]) =>
      ((time.dropEnd 2).toString.replace "." "").toNat?.map (name, ·)
    | _ => none

def replayedInParallel (report : String) : Bool :=
  let times := replayTimes report
  let time := fun (name : String) => (times.find? (·.1 == name)).map (·.2)
  match time "SlowKills.double_correct_rejects_identity", time "SlowKills.triple_correct_rejects_identity",
      times.back? with
  | some double, some triple, some (_, total) => 2 * total ≤ 2 * max double triple + min double triple
  | _, _, _ => false

abbrev Edits := List (System.FilePath × (String → Option String))

structure Exits where
  build : UInt32 := 0
  lint : UInt32 := 0
  test : UInt32 := 0
  comparator : UInt32 := 0
  grade : UInt32 := 0

def Exits.of (exits : Exits) : String → UInt32
  | "build" => exits.build
  | "lint" => exits.lint
  | "test" => exits.test
  | "comparator" => exits.comparator
  | _ => exits.grade

structure Mutant where
  name : String
  owner : Edits := []
  agent : Edits := []
  exits : Exits := {}

def replacing (old new : String) (text : String) : Option String :=
  if (text.splitOn old).length == 2 then some (text.replace old new) else none

def appending (addition : String) (text : String) : Option String := some (text ++ addition)

def matrixLayers : List String := ["build", "lint", "test", "comparator", "grade"]

def challengeFile : System.FilePath := "Challenge.lean"
def coreCodeFile : System.FilePath := "ConstantFolding" / "CoreCode.lean"
def worldCodeFile : System.FilePath := "ConstantFolding" / "WorldCode.lean"
def solutionFile : System.FilePath := "ConstantFolding" / "Solution.lean"

def restated : Edits := [
  (challengeFile, replacing "(h : fold (.lit n) = .lit m) : m = n := by" "(h : fold (.lit n) = .lit m) : n = m := by"),
  (challengeFile, replacing "= .lit m → m = n := by" "= .lit m → n = m := by")]

def mutants : List Mutant := [
  { name := "owner-unchanged" },
  { name := "owner-drops-kill", exits := { build := 1, lint := 1, grade := 3 }, owner := [
      (challengeFile, replacing "@[kills fold_normalizes] theorem fold_normalizes_rejects_identity : \
        ¬ ∀ e, normal (id e) = true := by\n  sorry\n\n" "")] },
  { name := "owner-restates-headline", exits := { lint := 2, comparator := 1, grade := 1 }, owner := restated },
  { name := "owner-breaks-solution", exits := { build := 1, lint := 1, test := 1, comparator := 1, grade := 1 }, owner := [
      ("ConstantFolding" / "CoreSpec.lean", replacing "@[expose] def Expr.isLit : Expr → Bool"
        "@[expose] def Expr.isLiteral : Expr → Bool"),
      ("ConstantFolding" / "CoreSpec.lean", replacing "!(a.isLit && b.isLit)" "!(a.isLiteral && b.isLiteral)")] },
  { name := "owner-adds-failing-test", exits := { test := 2, grade := 1 }, owner := [
      ("lakefile.lean", replacing "  testDriver := \"software_challenge/test_challenge\"\n"
        "  testDriver := \"software_challenge/test_challenge\"\n  testDriverArgs := #[\"own_test\"]\n"),
      ("lakefile.lean", appending "\nscript own_test do\n  return 2\n")] },
  { name := "agent-proves-restated-headline", owner := restated, agent := [
      (solutionFile, replacing "(h : fold (.lit n) = .lit m) : m = n := by" "(h : fold (.lit n) = .lit m) : n = m := by"),
      (solutionFile, replacing "  injection h with h\n  exact h.symm" "  injection h"),
      (solutionFile, replacing "= .lit m → m = n := by" "= .lit m → n = m := by")] },
  { name := "agent-honest", agent := [
      (coreCodeFile, appending "\ntheorem ConstantFolding.fold_fold (e : ConstantFolding.Expr) :\n    \
        ConstantFolding.fold (ConstantFolding.fold e) = ConstantFolding.fold e :=\n  \
        ConstantFolding.fold_eq_self_of_normal _ (ConstantFolding.normal_fold e)\n")] },
  { name := "agent-implemented-by", exits := { lint := 1, grade := 1 }, agent := [
      (coreCodeFile, replacing "def fold : Expr → Expr\n"
        "def foldAtRuntime : Expr → Expr := id\n\n@[implemented_by foldAtRuntime]\ndef fold : Expr → Expr\n")] },
  { name := "agent-forges-proof", exits := { comparator := 1, grade := 1 }, agent := [
      (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
        fold_eq_self_of_normal (fold e) (normal_fold e)"
        "set_option debug.skipKernelTC true in\nrun_meta Lean.addDecl (.thmDecl { name := `ConstantFolding.fold_forged, \
        levelParams := [], value := Lean.mkConst ``True.intro, \
        type := .forallE `e (Lean.mkConst ``Expr) (Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.one]) \
        (Lean.mkConst ``Expr) (Lean.mkApp (Lean.mkConst ``fold) (.bvar 0)) (.bvar 0)) .default })\n\n\
        theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  fold_forged (fold e)")] },
  { name := "agent-drops-checks", exits := { lint := 2, grade := 1 }, agent := [
      (worldCodeFile, replacing "Check AddAgrees nativeAdd : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71\n" ""),
      (worldCodeFile, replacing "Check AddAgrees nativeAdd := do" "def probeAdd : IO Unit := do")] },
  { name := "agent-failing-check", exits := { test := 1, grade := 1 }, agent := [
      (worldCodeFile, replacing "unless nativeAdd a b - a == b do" "unless nativeAdd a b - a == b + 1 do")] },
  { name := "agent-edits-challenge", exits := { build := 1, lint := 1, comparator := 1, grade := 1 }, agent := [
      (challengeFile, appending "\ntheorem graded : True := trivial\n")] },
  { name := "agent-adds-owned-file", exits := { build := 1, lint := 1, grade := 1 }, agent := [
      ("ConstantFolding" / "CoreSpec" / "Extra.lean",
        appending "module\n\npublic section\n\ntheorem ConstantFolding.extra : True := trivial\n")] },
  { name := "agent-weakens-solution", exits := { lint := 2, comparator := 1, grade := 1 }, agent := [
      (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :="
        "theorem fold_idempotent (e : Expr) (_ : normal e = true) : fold (fold e) = fold e :=")] },
  { name := "agent-drops-kill-proof", exits := { lint := 2, comparator := 1, grade := 1 }, agent := [
      (solutionFile, replacing "theorem fold_normalizes_rejects_identity : ¬ ∀ e, normal (id e) = true := by\n  \
        intro h\n  exact absurd (h (.add (.lit 1) (.lit 2))) (by decide)\n\n" "")] },
  { name := "agent-proves-outside-solution", exits := { lint := 2, comparator := 1, grade := 1 }, agent := [
      (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
        fold_eq_self_of_normal (fold e) (normal_fold e)\n\n" ""),
      ("ConstantFolding" / "Proofs.lean", appending "module\n\npublic import ConstantFolding.Solution\n\n\
        public section\n\nnamespace ConstantFolding\n\ntheorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
        fold_eq_self_of_normal (fold e) (normal_fold e)\n\nend ConstantFolding\n")] }]

def declaredIn (challenge : String) : Array String × Array String := Id.run do
  let mut scope : List String := []
  let mut theorems := #[]
  let mut holes := #[]
  for line in challenge.splitOn "\n" do
    let words := (line.splitOn " ").filter (!·.isEmpty)
    let qualified := fun (name : String) => ".".intercalate (scope.reverse ++ [name])
    match words with
    | "namespace" :: name :: _ => scope := name :: scope
    | "end" :: _ :: _ => scope := scope.drop 1
    | "def" :: name :: _ => if line.endsWith ":= sorry" then holes := holes.push (qualified name)
    | _ =>
      match (words.dropWhile (· != "theorem")).drop 1 with
      | name :: _ => theorems := theorems.push (qualified name)
      | [] => pure ()
  return (theorems, holes)

def comparatorConfigOf (challenge : String) : String :=
  let (theorems, holes) := declaredIn challenge
  (Json.mkObj [("challenge_module", toJson "Challenge"), ("solution_module", toJson "ConstantFolding.Solution"),
    ("theorem_names", toJson theorems), ("definition_names", toJson holes),
    ("permitted_axioms", toJson #["propext", "Quot.sound", "Classical.choice"])]).pretty

def scrubbedEnv : Array (String × Option String) :=
  #[("GIT_DIR", none), ("GIT_WORK_TREE", none), ("GIT_INDEX_FILE", none), ("SOFTWARE_CHALLENGE_JOBS", some "1")]

def runIn (dir : System.FilePath) (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := dir, env := scrubbedEnv }

def succeedIn (dir : System.FilePath) (cmd : String) (args : Array String) : IO Unit := do
  let out ← runIn dir cmd args
  unless out.exitCode == 0 do
    throw <| IO.userError s!"{cmd} {" ".intercalate args.toList} failed in {dir}:\n{out.stdout}{out.stderr}"

def gitIn (dir : System.FilePath) (args : Array String) : IO Unit :=
  succeedIn dir "git" (#["-c", "user.name=matrix", "-c", "user.email=matrix@localhost",
    "-c", "commit.gpgsign=false"] ++ args)

def runRetrying (dir : System.FilePath) (cmd : String) (args : Array String) : IO IO.Process.Output := do
  let mut out ← runIn dir cmd args
  for _ in [0:3] do
    unless (out.stdout ++ out.stderr).contains "bwrap: Can't bind mount" do break
    IO.sleep 20000
    out ← runIn dir cmd args
  return out

def comparatorVerdicts : Array String := #["kernel rejected the solution", "theorem statement do not match",
  "constant kind don't match", "Const not found in solution", "Const does not match between challenge and target",
  "Solution constant is not a definition", "Solution constant is not a theorem", "Illegal axiom detected",
  "is not permitted; it is used by"]

def stepLayers : List String := ["build", "lint", "test", "comparator"]

def layerOutput (lake : String) (dir : System.FilePath) : String → IO IO.Process.Output
  | "comparator" => do
    let config := dir / ".lake" / "matrix-comparator.json"
    IO.FS.writeFile config (comparatorConfigOf (← IO.FS.readFile (dir / challengeFile)))
    let built ← runIn dir lake #["build", "Challenge"]
    if built.exitCode == 0 then runRetrying dir lake #["comparator", "--config", config.toString] else pure built
  | layer => runIn dir lake #[layer]

def applyEdits (dir : System.FilePath) (m : Mutant) (edits : Edits) : IO Unit := do
  for (file, edit) in edits do
    IO.FS.createDirAll (dir / file).parent.get!
    let text ← if ← (dir / file).pathExists then IO.FS.readFile (dir / file) else pure ""
    let some edited := edit text | throw <| IO.userError s!"{m.name}: an edit of {file} no longer applies"
    IO.FS.writeFile (dir / file) edited

def gradeOf (statement : UInt32) (changesOwned : Bool) (code : String → UInt32) (verdict : Bool) : UInt32 :=
  if statement != 0 then 3
  else if changesOwned || stepLayers.any (fun layer => layer != "comparator" && code layer != 0) then 1
  else if code "comparator" == 0 then 0
  else if code "comparator" == 1 && verdict then 1
  else 3

def revert (lake : String) (copy : System.FilePath) (config : String) (m : Mutant) : IO Unit := do
  gitIn copy #["checkout", "-q", "--", "."]
  gitIn copy #["clean", "-fdq"]
  IO.FS.writeFile (copy / "comparator.json") config
  let rebuilt ← runIn copy lake #["build"]
  let idle ← runIn copy lake #["build", "--no-build"]
  let status ← runIn copy "git" #["status", "--porcelain"]
  unless rebuilt.exitCode == 0 && idle.exitCode == 0 && status.stdout.isEmpty &&
      (← IO.FS.readFile (copy / "comparator.json")) == config do
    throw <| IO.userError s!"{m.name}: reverting it left {copy} unlike the base, so later mutants would see its \
      state:\n{rebuilt.stdout}{rebuilt.stderr}{idle.stdout}{idle.stderr}{status.stdout}"

def runMutant (lake : String) (copy : System.FilePath) (owned : Array String) (config : String) (m : Mutant) :
    IO (Array (String × UInt32 × Nat) × String) := do
  let mut log := ""
  unless m.owner.isEmpty do
    applyEdits copy m m.owner
    IO.FS.removeFile (copy / "owned.lock")
    unless m.agent.isEmpty do
      let recorded ← runIn copy lake #["build"]
      log := log ++ s!"--- {m.name} owner build exit {recorded.exitCode}\n{recorded.stdout}{recorded.stderr}"
  applyEdits copy m m.agent
  let mut cells := #[]
  let mut verdict := false
  for layer in stepLayers do
    let start ← IO.monoMsNow
    let out ← layerOutput lake copy layer
    cells := cells.push (layer, out.exitCode, (← IO.monoMsNow) - start)
    log := log ++ s!"--- {m.name} {layer} exit {out.exitCode}\n{out.stdout}{out.stderr}"
    if layer == "comparator" then verdict := comparatorVerdicts.any ((out.stdout ++ out.stderr).contains ·)
  let start ← IO.monoMsNow
  let statement ← if m.owner.isEmpty then pure (0 : UInt32) else do
    let checked ← runIn copy lake #["build", ":softwareChallengeStatement"]
    log := log ++ s!"--- {m.name} statement check exit {checked.exitCode}\n{checked.stdout}{checked.stderr}"
    pure checked.exitCode
  let changesOwned := m.agent.any fun (file, _) => owned.contains file.toString
  let code := fun (layer : String) => ((cells.find? (·.1 == layer)).map (·.2.1)).getD 0
  cells := cells.push ("grade", gradeOf statement changesOwned code verdict, (← IO.monoMsNow) - start)
  revert lake copy config m
  return (cells, log)

def endToEnd : List (String × UInt32) := [("agent-honest", 0), ("agent-edits-challenge", 1)]

def gradeEndToEnd (lake : String) (base : System.FilePath) : IO (Array (String × UInt32 × UInt32 × String)) := do
  let mut results := #[]
  for (name, expected) in endToEnd do
    let some m := mutants.find? (·.name == name) | throw <| IO.userError s!"no mutant {name}"
    gitIn base #["checkout", "-q", "-b", name]
    applyEdits base m m.agent
    gitIn base #["add", "-A"]
    gitIn base #["commit", "-q", "-m", name]
    gitIn base #["checkout", "-q", "base"]
    let out ← runRetrying base lake #["exe", "grade", name]
    results := results.push (name, expected, out.exitCode, out.stdout ++ out.stderr)
  let absent ← runIn base lake #["exe", "grade", "absent"]
  return results.push ("a missing commit", 3, absent.exitCode, absent.stdout ++ absent.stderr)

def matrixBase (lake : String) (lsc root : System.FilePath) : IO System.FilePath := do
  let template := lsc / "Examples" / "ConstantFolding"
  let base := root / "base"
  for source in ← template.walkDir do
    let file := System.FilePath.mk (source.toString.drop (template.toString.length + 1)).toString
    if (← source.isDir) || file.components.head? == some ".lake" || file.toString == "comparator.json" then continue
    IO.FS.createDirAll (base / file).parent.get!
    IO.FS.writeBinFile (base / file) (← IO.FS.readBinFile source)
  for file in ["lakefile.lean", "lake-manifest.json"] do
    IO.FS.writeFile (base / file) ((← IO.FS.readFile (base / file)).replace "\"../..\"" s!"\"{lsc}\"")
  IO.FS.removeFile (base / "owned.lock")
  succeedIn base lake #["build"]
  gitIn base #["init", "-q"]
  gitIn base #["add", "-A"]
  gitIn base #["commit", "-q", "-m", "base"]
  gitIn base #["branch", "-M", "base"]
  return base

def cellOf (layer : String) (code : UInt32) : String :=
  if code == 0 then "accepted"
  else if layer == "lint" && code == 2 then "pending (2)"
  else if layer == "grade" && code == 3 then "cannot judge (3)"
  else s!"refused ({code})"

script test_matrix do
  let lake := (← getLake).toString
  let lsc ← IO.FS.realPath (← getRootPackage).dir
  let root := lsc / ".lake" / "build" / "matrix"
  if ← root.pathExists then IO.FS.removeDirAll root
  IO.FS.createDirAll root
  try
    let base ← matrixBase lake lsc root
    let config ← IO.FS.readFile (base / "comparator.json")
    let owned := ((← IO.FS.readFile (base / "owned.lock")).splitOn "\n").toArray.filterMap fun line =>
      match line.splitOn " " with
      | [_, file] => some file
      | _ => none
    let jobs := ((← IO.getEnv "SOFTWARE_CHALLENGE_JOBS").bind (·.toNat?)).getD
      (min 16 (System.Platform.Internal.getHardwareConcurrency ()).toNat)
    let copies ← (List.range (max 1 (min (jobs - 1) mutants.length))).mapM fun index => do
      let copy := root / s!"copy{index}"
      gitIn root #["clone", "-q", base.toString, copy.toString]
      return copy
    let graded ← IO.asTask (gradeEndToEnd lake base) (prio := .dedicated)
    let pending ← IO.mkRef mutants
    let results ← IO.mkRef (#[] : Array (Mutant × Array (String × UInt32 × Nat) × String))
    let workers ← copies.mapM fun copy => IO.asTask (prio := .dedicated) do
      succeedIn copy lake #["build"]
      repeat
        let some m ← pending.modifyGet (fun ms => (ms.head?, ms.drop 1)) | break
        let (cells, log) ← runMutant lake copy owned config m
        results.modify (·.push (m, cells, log))
    for task in workers do IO.ofExcept task.get
    let done := (← results.get).qsort fun a b => (mutants.findIdx (·.name == a.1.name)) < mutants.findIdx (·.name == b.1.name)
    let mut failed := false
    let mut rows := #[s!"| mutant | {" | ".intercalate matrixLayers} |",
      s!"|---|{"|".intercalate (matrixLayers.map fun _ => "---")}|"]
    for (m, cells, log) in done do
      let wrong := cells.filter fun (layer, code, _) => code != m.exits.of layer
      unless wrong.isEmpty do
        failed := true
        IO.eprintln s!"{m.name}: {", ".intercalate (wrong.map fun (layer, code, _) =>
          s!"{layer} exited {code}, expected {m.exits.of layer}").toList}\n{log}"
      rows := rows.push s!"| {m.name} | {" | ".intercalate (cells.map fun (layer, code, ms) =>
        let mark := if code == m.exits.of layer then "" else "**"
        s!"{mark}{cellOf layer code}{mark} {tenths ms}").toList} |"
    rows := rows.push "\nThe grade column follows from the base's statement check, the owned-file diff, and the four \
      steps; `lake exe grade` ran end to end on:"
    for (name, expected, code, log) in ← IO.ofExcept graded.get do
      if code != expected then
        failed := true
        IO.eprintln s!"lake exe grade on {name} exited {code}, expected {expected}:\n{log}"
      rows := rows.push s!"- {name}: exit {code}{if code == expected then "" else s!", expected {expected}"}"
    IO.FS.writeFile (lsc / ".lake" / "build" / "grade.md") ("\n".intercalate rows.toList ++ "\n")
    IO.println ("\n".intercalate rows.toList)
    return if failed then 1 else 0
  finally
    IO.FS.removeDirAll root

def sandboxFiles (lsc scratch : System.FilePath) : List (System.FilePath × String) := [
  ("hidden" / "lakefile.lean", "import Lake\nopen Lake DSL\npackage «hidden»\n"),
  ("consumer" / ".gitignore", "/.lake\n/comparator.json\n"),
  ("consumer" / "lakefile.lean", s!"import Lake\nopen Lake DSL\n\npackage «consumer» where\n  \
    builtinLint := true\n  lintDriver := \"software_challenge/lint_challenge\"\n\n\
    require software_challenge from \"{lsc}\"\nrequire hidden from \"{scratch / "hidden"}\"\n\n\
    @[default_target]\nlean_lib «Consumer» where\n  roots := #[`Consumer.Solution]\n  globs := #[.submodules `Consumer]\n\n\
    lean_lib «Challenge» where\n  leanOptions := #[⟨`warn.sorry, false⟩]\n\n{statementTarget}\n"),
  ("consumer" / "Challenge.lean", "module\n\nmeta import SoftwareChallenge\n\npublic section\n\n\
    def zero : Nat → Nat := sorry\n\ntheorem zero_zero : zero 0 = 0 := by\n  sorry\n\n\
    @[kills zero_zero] theorem zero_zero_rejects_one : ¬ (fun (_ : Nat) => 1) 0 = 0 := by\n  sorry\n"),
  ("consumer" / "Consumer" / "CoreCode.lean", "module\n\n@[expose] public section\n\ndef zero (_ : Nat) : Nat := 0\n"),
  ("consumer" / "Consumer" / "Solution.lean", "module\n\npublic import Consumer.CoreCode\nmeta import SoftwareChallenge\n\n\
    public section\n\ntheorem zero_zero : zero 0 = 0 := rfl\n\n\
    theorem zero_zero_rejects_one : ¬ (fun (_ : Nat) => 1) 0 = 0 := by decide\n")]

script test_sandbox do
  let lake := (← getLake).toString
  let lsc ← IO.FS.realPath (← getRootPackage).dir
  let scratch ← IO.FS.createTempDir
  try
    let consumer := scratch / "consumer"
    for (file, text) in sandboxFiles lsc scratch do
      IO.FS.createDirAll (scratch / file).parent.get!
      IO.FS.writeFile (scratch / file) text
    IO.FS.writeFile (consumer / "lean-toolchain") (← IO.FS.readFile (lsc / "lean-toolchain"))
    succeedIn consumer lake #["build"]
    let lint ← runIn consumer lake #["lint"]
    gitIn consumer #["init", "-q"]
    gitIn consumer #["add", "-A"]
    gitIn consumer #["commit", "-q", "-m", "consumer"]
    let grade ← runIn consumer lake #["exe", "grade", "HEAD"]
    let hides := "the comparator's sandbox hides package hidden"
    if lint.exitCode == 2 && (lint.stdout ++ lint.stderr).contains hides &&
        grade.exitCode == 3 && (grade.stdout ++ grade.stderr).contains hides then return 0
    IO.eprintln s!"a dependency under {scratch} was not reported: lake lint exited {lint.exitCode}, expected 2, and \
      lake exe grade exited {grade.exitCode}, expected 3:\n{lint.stdout}{lint.stderr}\n{grade.stdout}{grade.stderr}"
    return 1
  finally
    IO.FS.removeDirAll scratch

def ladder (lake : String) (steps : List (System.FilePath × Array String)) : IO (Option String) := do
  for (cwd, args) in steps do
    let out ← IO.Process.output { cmd := lake, args, cwd }
    unless out.exitCode == 0 do
      return some s!"`lake {" ".intercalate args.toList}` exited {out.exitCode} in {cwd}:\n{out.stdout}{out.stderr}"
  return none

@[test_driver] script test_library do
  let lake := (← getLake).toString
  let root := (← getRootPackage).dir
  let template := root / "Examples" / "ConstantFolding"
  let slow := root / "SoftwareChallengeTests" / "SlowKills"
  let start ← IO.monoMsNow
  let ladders := [[(root, #["build"]), (root, #["build", "grade", "SoftwareChallengeTests"]), (root, #["lint"])],
    [(template, #["build"]), (template, #["lint"]), (template, #["test"])],
    [(slow, #["build"]), (slow, #["lint"]), (slow, #["test"]), (slow, #["script", "run", "software_challenge/replay"])],
    [(root, #["script", "run", "test_sandbox"])]]
  if let some failure ← ladder lake ladders.head! then
    IO.eprintln s!"{failure}\nFix what it reports, then run `lake test`."
    return 1
  let tasks ← ladders.tail.mapM fun steps => IO.asTask (ladder lake steps) (prio := .dedicated)
  let failures := (← tasks.mapM fun task => IO.ofExcept task.get).filterMap id
  unless failures.isEmpty do
    IO.eprintln s!"{"\n".intercalate failures}\nFix what they report, then run `lake test`."
    return 1
  let report ← IO.FS.readFile (slow / ".lake" / "build" / "comparator.txt")
  unless replayedInParallel report do
    IO.eprintln s!"the two slow kills did not replay in about the time of the slower one:\n{report}\nFind what \
      serialized them in replayEach in lakefile.lean, then run `lake test`."
    return 1
  IO.println s!"Ladders passed in {tenths ((← IO.monoMsNow) - start)}"
  let code ← (← IO.Process.spawn { cmd := lake, args := #["script", "run", "test_matrix"], cwd := root }).wait
  IO.println s!"lake test took {tenths ((← IO.monoMsNow) - start)}"
  return code

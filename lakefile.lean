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
  "Challenge is unavailable; state the challenge in Challenge.lean and declare `lean_lib «Challenge»` in lakefile.lean"

def packageModules (pkg : Package) (challenge : Lake.Module) : FetchM (Array Lake.Module) := do
  let mut modules := #[]
  for root in (← (← pkg.defaultModules.fetch).await).push challenge do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || mod.name == challenge.name || modules.any (·.name == mod.name) do
        modules := modules.push mod
  return modules

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
    unless output.exitCode == 0 do IO.eprintln s!"lake comparator on {name}:\n{output.stdout}{output.stderr}"
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

def sandboxCovers : Array System.FilePath := #["/home", "/root", "/run", "/tmp", "/var"]

def within (dir root : System.FilePath) : Bool :=
  root.components.isPrefixOf dir.components

def hiddenFromSandbox (root : Package) : ScriptM (Array (Name × System.FilePath)) := do
  let rootDir ← IO.FS.realPath root.dir
  let mut hidden := #[]
  for pkg in (← getWorkspace).packages do
    let dir ← IO.FS.realPath pkg.dir
    unless within dir rootDir || !sandboxCovers.any (within dir ·) do
      hidden := hidden.push (pkg.baseName, dir)
  return hidden

def runChecks (lake : String) (pkg : Package) : ScriptM UInt32 := do
  let some challenge := pkg.findModule? `Challenge | do IO.eprintln challengeMissing; return 1
  let modules := (← runBuild do return Job.pure (← packageModules pkg challenge)).map (·.name)
  let runner := pkg.buildDir / "softwareChallenge" / "Checks.lean"
  IO.FS.createDirAll (pkg.buildDir / "softwareChallenge")
  IO.FS.writeFile runner <| "\n".intercalate <| ["import SoftwareChallenge"] ++
    (modules.map (s!"import {·}")).toList ++
    [s!"run_cmd SoftwareChallenge.runChecks #[{", ".intercalate (modules.map (s!"`{·}")).toList}]", ""]
  (← IO.Process.spawn { cmd := lake, args := #["lean", runner.toString], cwd := pkg.dir }).wait

script run_checks do
  runChecks (← getLake).toString (← getRootPackage)

script test_challenge do
  let lake := (← getLake).toString
  let pkg ← getRootPackage
  let hidden ← hiddenFromSandbox pkg
  for (name, dir) in hidden do
    IO.eprintln s!"the comparator's sandbox hides {name} at {dir}: it covers /home, /root, /run, /tmp \
      and /var; require {name} by git, so it lives in .lake/packages, or move it inside this package"
  unless hidden.isEmpty do return 1
  for args in [#["build"], #["build", ":softwareChallenge"], #["lint", "--builtin-lint"]] do
    let code ← (← IO.Process.spawn { cmd := lake, args, cwd := pkg.dir }).wait
    unless code == 0 do return code
  let code ← runChecks lake pkg
  unless code == 0 do return code
  let report ← IO.FS.readFile (pkg.buildDir / "softwareChallenge.txt")
  let unproved := (report.splitOn "\n").filter (·.endsWith "not yet proved)")
  unless unproved.isEmpty do
    IO.eprintln s!"{unproved.length} headlines or their witnesses are not yet proved, so the solution is not accepted:"
    for line in unproved do IO.eprintln s!"  {line}"
    return 1
  replayEach lake pkg.dir pkg.buildDir

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

lean_exe «grade» where
  root := `SoftwareChallenge.Grade

structure Mutant where
  name : String
  byOwner : Bool
  edits : List (System.FilePath × (String → Option String))
  refusedBy : List String

def replacing (old new : String) (text : String) : Option String :=
  if (text.splitOn old).length == 2 then some (text.replace old new) else none

def appending (addition : String) (text : String) : Option String := some (text ++ addition)

def matrixLayers : List String := ["compile", "comparator", "audit", "checks", "full"]

def challengeFile : System.FilePath := "Challenge.lean"
def coreCodeFile : System.FilePath := "ConstantFolding" / "CoreCode.lean"
def worldCodeFile : System.FilePath := "ConstantFolding" / "WorldCode.lean"
def solutionFile : System.FilePath := "ConstantFolding" / "Solution.lean"

def mutants : List Mutant := [
  { name := "owner-unchanged", byOwner := true, edits := [], refusedBy := [] },
  { name := "owner-misstates-headline", byOwner := true, refusedBy := ["comparator", "full"], edits := [
      (challengeFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e := by"
        "theorem fold_idempotent (e : Expr) : fold (fold e) = e := by"),
      (challengeFile, replacing "      (fun e => Expr.lit (eval (fun _ => 0) e + 1)) e := by" "      e := by")] },
  { name := "owner-drops-kill", byOwner := true, refusedBy := ["audit", "full"], edits := [
      (challengeFile, replacing "@[kills fold_normalizes] theorem fold_normalizes_rejects_identity : \
        ¬ ∀ e, normal (id e) = true := by\n  sorry\n\n" "")] },
  { name := "owner-drops-witness", byOwner := true, refusedBy := ["audit", "full"], edits := [
      (challengeFile, replacing "@[witness fold_keeps_literal] theorem fold_keeps_literal_applies :\n    \
        ∃ (n m : Nat), fold (.lit n) = .lit m := by\n  sorry\n" "")] },
  { name := "owner-duplicates-headline", byOwner := true, refusedBy := ["audit", "full"], edits := [
      (challengeFile, replacing "theorem fold_keeps_literal (n m : Nat)"
        "theorem fold_idempotent_again (x : Expr) : fold (fold x) = fold x := by\n  sorry\n\n\
        theorem fold_keeps_literal (n m : Nat)"),
      (challengeFile, replacing "@[kills fold_idempotent] theorem"
        "@[kills fold_idempotent, kills fold_idempotent_again] theorem"),
      (solutionFile, replacing "theorem fold_keeps_literal (n m : Nat) (h"
        "theorem fold_idempotent_again (x : Expr) : fold (fold x) = fold x :=\n  fold_idempotent x\n\n\
        theorem fold_keeps_literal (n m : Nat) (h")] },
  { name := "agent-honest", byOwner := false, refusedBy := [], edits := [
      (coreCodeFile, appending "\ntheorem ConstantFolding.fold_fold (e : ConstantFolding.Expr) :\n    \
        ConstantFolding.fold (ConstantFolding.fold e) = ConstantFolding.fold e :=\n  \
        ConstantFolding.fold_eq_self_of_normal _ (ConstantFolding.normal_fold e)\n")] },
  { name := "agent-sorry", byOwner := false, refusedBy := ["comparator", "audit", "full"], edits := [
      (solutionFile, replacing "normal (fold e) = true :=\n  normal_fold e" "normal (fold e) = true :=\n  sorry")] },
  { name := "agent-implemented-by", byOwner := false, refusedBy := ["audit", "full"], edits := [
      (coreCodeFile, replacing "def fold : Expr → Expr\n"
        "def foldAtRuntime : Expr → Expr := id\n\n@[implemented_by foldAtRuntime]\ndef fold : Expr → Expr\n")] },
  { name := "agent-io-in-core", byOwner := false, refusedBy := ["audit", "full"], edits := [
      (coreCodeFile, appending "\ndef ConstantFolding.announce : IO Unit := pure ()\n")] },
  { name := "agent-core-imports-world", byOwner := false, refusedBy := ["audit", "full"], edits := [
      (coreCodeFile, replacing "public import ConstantFolding.CoreSpec\n"
        "public import ConstantFolding.CoreSpec\npublic import ConstantFolding.WorldSpec\n")] },
  { name := "agent-axiom", byOwner := false, refusedBy := ["comparator", "audit", "full"], edits := [
      (coreCodeFile, appending "\naxiom ConstantFolding.fold_twice (e : ConstantFolding.Expr) :\n    \
        ConstantFolding.fold (ConstantFolding.fold e) = ConstantFolding.fold e\n"),
      (solutionFile, replacing "  fold_eq_self_of_normal (fold e) (normal_fold e)" "  fold_twice e")] },
  { name := "agent-drops-checks", byOwner := false, refusedBy := ["audit", "full"], edits := [
      (worldCodeFile, replacing "Check AddAgrees nativeAdd : nativeAdd (2 ^ 70) (2 ^ 70) = 2 ^ 71\n" ""),
      (worldCodeFile, replacing "Check AddAgrees nativeAdd := do" "def probeAdd : IO Unit := do")] },
  { name := "agent-failing-check", byOwner := false, refusedBy := ["checks", "full"], edits := [
      (worldCodeFile, replacing "unless nativeAdd a b - a == b do" "unless nativeAdd a b - a == b + 1 do")] },
  { name := "agent-edits-challenge", byOwner := false, refusedBy := ["comparator", "audit", "full"], edits := [
      (challengeFile, appending "\ntheorem graded : True := trivial\n")] },
  { name := "agent-adds-owned-file", byOwner := false, refusedBy := ["audit", "full"], edits := [
      ("ConstantFolding" / "CoreSpec" / "Extra.lean",
        appending "module\n\npublic section\n\ntheorem ConstantFolding.extra : True := trivial\n")] },
  { name := "agent-weakens-solution", byOwner := false, refusedBy := ["comparator", "full"], edits := [
      (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :="
        "theorem fold_idempotent (e : Expr) (_ : normal e = true) : fold (fold e) = fold e :=")] }]

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
  #[("GIT_DIR", none), ("GIT_WORK_TREE", none), ("GIT_INDEX_FILE", none), ("SOFTWARE_CHALLENGE_JOBS", some "2")]

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

def layerOutput (lake : String) (dir : System.FilePath) (m : Mutant) : String → IO IO.Process.Output
  | "compile" => runIn dir lake #["build"]
  | "comparator" => do
    IO.FS.writeFile (dir / "comparator.json") (comparatorConfigOf (← IO.FS.readFile (dir / challengeFile)))
    let built ← runIn dir lake #["build", "Challenge"]
    let out ← if built.exitCode == 0 then runRetrying dir lake #["comparator"] else pure built
    IO.FS.removeFile (dir / "comparator.json")
    return out
  | "audit" => runIn dir lake #["build", ":softwareChallenge"]
  | "checks" => runIn dir lake #["script", "run", "software_challenge/run_checks"]
  | _ => if m.byOwner then runRetrying dir lake #["test"] else do
    gitIn dir #["checkout", "-q", "base"]
    runRetrying dir lake #["exe", "grade", "candidate"]

def runMutant (lake : String) (base root : System.FilePath) (m : Mutant) :
    IO (Array (String × UInt32 × Nat) × String) := do
  let dir := root / m.name
  succeedIn root "cp" #["-a", base.toString, dir.toString]
  unless m.byOwner do gitIn dir #["checkout", "-q", "-b", "candidate"]
  for (file, edit) in m.edits do
    IO.FS.createDirAll (dir / file).parent.get!
    let text ← if ← (dir / file).pathExists then IO.FS.readFile (dir / file) else pure ""
    let some edited := edit text | throw <| IO.userError s!"{m.name}: an edit of {file} no longer applies"
    IO.FS.writeFile (dir / file) edited
  if m.byOwner then IO.FS.removeFile (dir / "owned.lock")
  else
    gitIn dir #["add", "-A"]
    gitIn dir #["commit", "-q", "-m", m.name]
  let mut cells := #[]
  let mut log := ""
  for layer in matrixLayers do
    let start ← IO.monoMsNow
    let out ← layerOutput lake dir m layer
    cells := cells.push (layer, out.exitCode, (← IO.monoMsNow) - start)
    log := log ++ s!"--- {m.name} {layer} exit {out.exitCode}\n{out.stdout}{out.stderr}"
  return (cells, log)

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
  succeedIn base lake #["build", ":softwareChallenge"]
  discard <| runIn base lake #["exe", "grade"]
  gitIn base #["init", "-q"]
  gitIn base #["add", "-A"]
  gitIn base #["commit", "-q", "-m", "base"]
  gitIn base #["branch", "-M", "base"]
  return base

def verdict (m : Mutant) (layer : String) (code : UInt32) : String × Bool :=
  let expected := m.refusedBy.contains layer
  let refused := code != 0
  let cell := if refused then s!"refused ({code})" else "accepted"
  let wellFormed := m.byOwner || layer != "full" || code == 0 || code == 1
  (cell, expected == refused && wellFormed)

script test_matrix do
  let lake := (← getLake).toString
  let lsc ← IO.FS.realPath (← getRootPackage).dir
  let root := lsc / ".lake" / "build" / "matrix"
  if ← root.pathExists then IO.FS.removeDirAll root
  IO.FS.createDirAll root
  try
    let base ← matrixBase lake lsc root
    let absent ← runIn base lake #["exe", "grade", "absent"]
    let pending ← IO.mkRef mutants
    let results ← IO.mkRef (#[] : Array (Mutant × Array (String × UInt32 × Nat) × String))
    let worker : IO Unit := do
      repeat
        let some m ← pending.modifyGet (fun ms => (ms.head?, ms.drop 1)) | break
        let (cells, log) ← runMutant lake base root m
        results.modify (·.push (m, cells, log))
    let slots := ((← IO.getEnv "SOFTWARE_CHALLENGE_JOBS").bind (·.toNat?)).getD 4
    let workers ← (List.range (min mutants.length (max 1 slots))).mapM fun _ => IO.asTask worker (prio := .dedicated)
    for task in workers do IO.ofExcept task.get
    let done := (← results.get).qsort fun a b => (mutants.findIdx (·.name == a.1.name)) < mutants.findIdx (·.name == b.1.name)
    let mut failed := absent.exitCode != 3
    if failed then IO.eprintln s!"grade on a missing commit exited {absent.exitCode}, expected 3"
    let mut rows := #[s!"| mutant | {" | ".intercalate matrixLayers} |",
      s!"|---|{"|".intercalate (matrixLayers.map fun _ => "---")}|"]
    for (m, cells, log) in done do
      let judged := cells.map fun (layer, code, ms) => (layer, verdict m layer code, ms)
      if judged.any (!·.2.1.2) then
        failed := true
        IO.eprintln s!"{m.name} expected refusal by {m.refusedBy}, got:\n{log}"
      rows := rows.push s!"| {m.name} | {" | ".intercalate (judged.map fun (_, (cell, ok), ms) =>
        s!"{if ok then "" else "**"}{cell}{if ok then "" else "**"} {tenths ms}").toList} |"
    rows := rows.push s!"\ngrade on a missing commit: exit {absent.exitCode}"
    IO.FS.writeFile (lsc / ".lake" / "build" / "grade.md") ("\n".intercalate rows.toList ++ "\n")
    return if failed then 1 else 0
  finally
    IO.FS.removeDirAll root

script test_sandbox do
  let lake := (← getLake).toString
  let lsc ← IO.FS.realPath (← getRootPackage).dir
  let scratch ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (scratch / "hidden")
    IO.FS.writeFile (scratch / "hidden" / "lakefile.lean") "import Lake\nopen Lake DSL\npackage «hidden»\n"
    IO.FS.createDirAll (scratch / "consumer")
    IO.FS.writeFile (scratch / "consumer" / "lean-toolchain") (← IO.FS.readFile (lsc / "lean-toolchain"))
    IO.FS.writeFile (scratch / "consumer" / "lakefile.lean") s!"import Lake\nopen Lake DSL\n\
      package «consumer» where\n  testDriver := \"software_challenge/test_challenge\"\n\
      require software_challenge from \"{lsc}\"\nrequire hidden from \"{scratch / "hidden"}\"\n"
    let out ← runIn (scratch / "consumer") lake #["test"]
    if out.exitCode != 0 && out.stderr.contains "the comparator's sandbox hides hidden" then return 0
    IO.eprintln s!"a dependency under {scratch} was not refused:\n{out.stdout}{out.stderr}"
    return 1
  finally
    IO.FS.removeDirAll scratch

@[test_driver] script test do
  let lake := (← getLake).toString
  let root := (← getRootPackage).dir
  let slow := root / "SoftwareChallengeTests" / "SlowKills"
  for (args, cwd) in [(#["build"], root), (#["lint"], root), (#["build", "SoftwareChallengeTests"], root),
      (#["test"], root / "Examples" / "ConstantFolding"), (#["test"], slow),
      (#["script", "run", "test_sandbox"], root), (#["script", "run", "test_matrix"], root)] do
    let code ← (← IO.Process.spawn { cmd := lake, args, cwd }).wait
    unless code == 0 do return code
  let report ← IO.FS.readFile (slow / ".lake" / "build" / "comparator.txt")
  unless replayedInParallel report do
    IO.eprintln s!"the two slow kills did not replay in about the time of the slower one:\n{report}"
    return 1
  return 0

package_facet softwareChallenge pkg : Unit := do
  let some audit ← findModule? `SoftwareChallenge.Audit | error "SoftwareChallenge.Audit is unavailable"
  let some challenge := pkg.findModule? `Challenge | error challengeMissing
  let catalog ← packageModules pkg challenge
  for mod in catalog do
    if (← (← mod.imports.fetch).await).any (·.name == challenge.name) then
      error s!"{mod.name} imports {challenge.name}, which the comparator checks the solution against; \
        import the CoreSpec and WorldSpec modules it imports instead"
  let mut job := (Job.nil.mix (← audit.leanArts.fetch)).mix (← challenge.leanArts.fetch)
  for mod in catalog do
    job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do
    addTrace (← BuildTrace.compute (TextFilePath.mk (__dir__ / "Audit.lean")))
    for file in ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "owned.lock"] do
      if ← (pkg.dir / file).pathExists then addTrace (← BuildTrace.compute (TextFilePath.mk (pkg.dir / file)))
    let report := pkg.buildDir / "softwareChallenge.txt"
    unless ← (pkg.dir / "comparator.json").pathExists do
      if ← (report.addExtension "trace").pathExists then IO.FS.removeFile (report.addExtension "trace")
    buildUnlessUpToDate report (← getTrace) (report.addExtension "trace") do
      let out ← IO.Process.output {
        cmd := (← getLean).toString
        args := #["--run", (__dir__ / "Audit.lean").toString] ++
          (if pkg.leanExes.isEmpty then #[] else #["--executable"]) ++
            #[challenge.relLeanFile.toString, challenge.oleanFile.toString] ++
          catalog.map fun mod => s!"{mod.name}={mod.relLeanFile}"
        cwd := some pkg.dir
        env := ← getAugmentedEnv
      }
      unless out.exitCode == 0 do
        logError (out.stdout ++ out.stderr)
        error "the challenge audit failed; fix the errors above"
      IO.FS.writeFile report out.stdout
      logInfo ("\n" ++ out.stdout)

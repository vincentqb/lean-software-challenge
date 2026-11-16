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
      let output ← IO.Process.output { cmd := lake, args := #["comparator", "--config", file.toString], cwd := dir }
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

script test_challenge do
  let lake := (← getLake).toString
  let pkg ← getRootPackage
  let run := fun (args : Array String) => do (← IO.Process.spawn { cmd := lake, args, cwd := pkg.dir }).wait
  for args in [#["build"], #["lint", "--builtin-lint"]] do
    let code ← run args
    unless code == 0 do return code
  let some challenge := pkg.findModule? `Challenge | do IO.eprintln challengeMissing; return 1
  let modules := (← runBuild do return Job.pure (← packageModules pkg challenge)).map (·.name)
  let runner := pkg.buildDir / "softwareChallenge" / "Checks.lean"
  IO.FS.createDirAll (pkg.buildDir / "softwareChallenge")
  IO.FS.writeFile runner <| "\n".intercalate <| ["import SoftwareChallenge"] ++
    (modules.map (s!"import {·}")).toList ++
    [s!"run_cmd SoftwareChallenge.runChecks #[{", ".intercalate (modules.map (s!"`{·}")).toList}]", ""]
  let code ← run #["lean", runner.toString]
  unless code == 0 do return code
  -- The comparator needs every headline and witness proved; name the ones that are not instead of
  -- letting it fail on a constant the solution does not declare.
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

@[test_driver] script test do
  let lake := (← getLake).toString
  let root := (← getRootPackage).dir
  let slow := root / "SoftwareChallengeTests" / "SlowKills"
  for (args, cwd) in [(#["build"], root), (#["lint"], root), (#["build", "SoftwareChallengeTests"], root),
      (#["test"], root / "Examples" / "ConstantFolding"), (#["test"], slow),
      (#["script", "run", "test_grade"], root)] do
    let code ← (← IO.Process.spawn { cmd := lake, args, cwd }).wait
    unless code == 0 do return code
  let report ← IO.FS.readFile (slow / ".lake" / "build" / "comparator.txt")
  unless replayedInParallel report do
    IO.eprintln s!"the two slow kills did not replay in about the time of the slower one:\n{report}"
    return 1
  return 0

def gradeCandidates : List (String × System.FilePath × String × UInt32) := [
  ("edits-challenge", "Challenge.lean", "theorem graded : True := trivial\n", 1),
  ("adds-core-spec", "ConstantFolding" / "CoreSpec" / "Extra.lean",
    "module\n\npublic section\n\ntheorem ConstantFolding.extra : True := trivial\n", 1),
  ("honest", "ConstantFolding" / "CoreCode.lean",
    "\ntheorem ConstantFolding.fold_fold (e : ConstantFolding.Expr) :\n    \
      ConstantFolding.fold (ConstantFolding.fold e) = ConstantFolding.fold e :=\n  \
      ConstantFolding.fold_eq_self_of_normal _ (ConstantFolding.normal_fold e)\n", 0)]

script test_grade do
  let lake := (← getLake).toString
  let lsc ← IO.FS.realPath (← getRootPackage).dir
  let template := lsc / "Examples" / "ConstantFolding"
  let scratch ← IO.FS.createTempDir
  let challenge := scratch / "constant_folding"
  let run (cmd : String) (args : Array String) : IO IO.Process.Output := IO.Process.output
    { cmd, args, cwd := challenge, env := #[("GIT_DIR", none), ("GIT_WORK_TREE", none), ("GIT_INDEX_FILE", none)] }
  let succeed (cmd : String) (args : Array String) : IO Unit := do
    let out ← run cmd args
    unless out.exitCode == 0 do throw <| IO.userError s!"{cmd} {" ".intercalate args.toList} failed:\n{out.stdout}{out.stderr}"
  let git (args : Array String) :=
    succeed "git" (#["-c", "user.name=grade", "-c", "user.email=grade@localhost", "-c", "commit.gpgsign=false"] ++ args)
  try
    for source in ← template.walkDir do
      let file := System.FilePath.mk (source.toString.drop (template.toString.length + 1)).toString
      if (← source.isDir) || file.components.head? == some ".lake" || file.toString == "comparator.json" then continue
      IO.FS.createDirAll (challenge / file).parent.get!
      IO.FS.writeBinFile (challenge / file) (← IO.FS.readBinFile source)
    for file in ["lakefile.lean", "lake-manifest.json"] do
      IO.FS.writeFile (challenge / file) ((← IO.FS.readFile (challenge / file)).replace "\"../..\"" s!"\"{lsc}\"")
    IO.FS.removeFile (challenge / "owned.lock")
    succeed lake #["build"]
    git #["init", "-q"]
    git #["add", "-A"]
    git #["commit", "-q", "-m", "base"]
    git #["branch", "-M", "base"]
    for (candidate, file, addition, _) in gradeCandidates do
      git #["checkout", "-q", "-b", candidate, "base"]
      IO.FS.createDirAll (challenge / file).parent.get!
      let h ← IO.FS.Handle.mk (challenge / file) .append
      h.putStr addition
      h.flush
      git #["add", "-A"]
      git #["commit", "-q", "-m", candidate]
    git #["checkout", "-q", "base"]
    let mut failed := false
    for (candidate, expected) in ("absent", 3) :: gradeCandidates.map fun (c, _, _, e) => (c, e) do
      let out ← run lake #["script", "run", "software_challenge/grade", candidate]
      unless out.exitCode == expected do
        IO.eprintln s!"grade {candidate} exited {out.exitCode}, expected {expected}:\n{out.stdout}{out.stderr}"
        failed := true
    return if failed then 1 else 0
  finally
    IO.FS.removeDirAll scratch

script grade (args) do
  let [candidate] := args
    | do IO.eprintln "usage: lake script run software_challenge/grade <candidate commit>"; return 3
  let base := (← getRootPackage).dir
  let gitPrefix : IO.Process.SpawnArgs :=
    { cmd := "git", args := #["rev-parse", "--show-prefix"], cwd := some base }
  let prefixInRepo := String.ofList ((← IO.Process.output gitPrefix).stdout.toList.filter (· != '\n'))
  let lake := (← getLake).toString
  let run (cmd : String) (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
    (← IO.Process.spawn { cmd, args, cwd := some cwd }).wait
  let ownedFiles (dir : System.FilePath) : IO (Array String) := do
    let report ← IO.FS.readFile (dir / ".lake" / "build" / "softwareChallenge.txt")
    let some line := (report.splitOn "\n").find? (·.startsWith "Owned: ")
      | throw <| IO.userError s!"{dir} reports no owned files"
    return ((line.splitOn " ").drop 1).toArray
  unless (← run lake #["build"] base) == 0 do
    IO.eprintln "cannot grade: the base does not pass"; return 3
  let owned ← ownedFiles base
  match ← run "git" (#["diff", "--quiet", candidate, "--"] ++ owned) base with
  | 0 => pure ()
  | 1 =>
    discard <| run "git" (#["diff", "--stat", candidate, "--"] ++ owned) base
    IO.eprintln s!"refused: {candidate} changes files the owner decides"; return 1
  | _ => IO.eprintln s!"cannot grade: git cannot compare {candidate}"; return 3
  let scratch ← IO.FS.createTempDir
  let worktree := scratch / "candidate"
  let checkout := worktree / prefixInRepo
  try
    unless (← run "git" #["worktree", "add", "--detach", worktree.toString, candidate] base) == 0 do
      return 3
    unless (← run lake #["build"] checkout) == 0 do return 1
    unless (← ownedFiles checkout) == owned do
      IO.eprintln s!"refused: {candidate} adds files the owner decides"; return 1
    if (← run lake #["test"] checkout) == 0 then return 0 else return 1
  finally
    discard <| run "git" #["worktree", "remove", "--force", worktree.toString] base
    IO.FS.removeDirAll scratch

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

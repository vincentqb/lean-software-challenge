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

script test_challenge do
  let lake := (← getLake).toString
  let pkg ← getRootPackage
  let run := fun (args : Array String) => do (← IO.Process.spawn { cmd := lake, args, cwd := pkg.dir }).wait
  for args in [#["build"], #["lint"]] do
    let code ← run args
    unless code == 0 do return code
  let some challenge ← findModule? `Challenge | do IO.eprintln challengeMissing; return 1
  let modules := (← runBuild do return Job.pure (← packageModules pkg challenge)).map (·.name)
  let runner := pkg.buildDir / "softwareChallenge" / "Checks.lean"
  IO.FS.createDirAll (pkg.buildDir / "softwareChallenge")
  IO.FS.writeFile runner <| "\n".intercalate <| ["import SoftwareChallenge"] ++
    (modules.map (s!"import {·}")).toList ++
    [s!"run_cmd SoftwareChallenge.runChecks #[{", ".intercalate (modules.map (s!"`{·}")).toList}]", ""]
  for args in [#["lean", runner.toString], #["comparator"]] do
    let code ← run args
    unless code == 0 do return code
  return 0

@[test_driver] script test do
  let lake := (← getLake).toString
  let root := (← getRootPackage).dir
  for (args, cwd) in [(#["build"], root), (#["lint"], root), (#["build", "SoftwareChallengeTests"], root),
      (#["test"], root / "Examples" / "ConstantFolding")] do
    let code ← (← IO.Process.spawn { cmd := lake, args, cwd }).wait
    unless code == 0 do return code
  return 0

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
  let some challenge ← findModule? `Challenge | error challengeMissing
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
          (if pkg.leanExes.isEmpty then #[] else #["--executable"]) ++ #[challenge.relLeanFile.toString] ++
          catalog.map fun mod => s!"{mod.name}={mod.relLeanFile}"
        cwd := some pkg.dir
        env := ← getAugmentedEnv
      }
      unless out.exitCode == 0 do
        logError (out.stdout ++ out.stderr)
        error "the challenge audit failed; fix the errors above"
      IO.FS.writeFile report out.stdout
      logInfo ("\n" ++ out.stdout)

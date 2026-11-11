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
    for step in [#["comparator"], #["test"]] do
      unless (← run lake step checkout) == 0 do return 1
    return 0
  finally
    discard <| run "git" #["worktree", "remove", "--force", worktree.toString] base
    IO.FS.removeDirAll scratch

package_facet softwareChallenge pkg : Unit := do
  let some audit ← findModule? `SoftwareChallenge.Audit | error "SoftwareChallenge.Audit is unavailable"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (pkg.dir / "comparator.json"))
  let challenge ← IO.ofExcept <| config.getObjValAs? String "challenge_module"
  let some manifest ← findModule? challenge.toName | error s!"{challenge} is unavailable"
  let mut catalog : Array Name := #[]
  let mut job := (Job.nil.mix (← audit.leanArts.fetch)).mix (← manifest.leanArts.fetch)
  for root in ← (← pkg.defaultModules.fetch).await do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || catalog.contains mod.name do
        catalog := catalog.push mod.name
        job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do
    for file in [pkg.dir / "Audit.lean", pkg.dir / "comparator.json"] do
      addTrace (← BuildTrace.compute (TextFilePath.mk file))
    let report := pkg.buildDir / "softwareChallenge.txt"
    let upToDate ← buildUnlessUpToDate? report (← getTrace) (report.addExtension "trace") do
      IO.FS.writeFile report (← captureProc {
        cmd := (← getLean).toString
        args := #["--run", (pkg.dir / "Audit.lean").toString] ++ catalog.map Name.toString
        cwd := some pkg.dir
        env := ← getAugmentedEnv
      })
    unless upToDate do logInfo (← IO.FS.readFile report)

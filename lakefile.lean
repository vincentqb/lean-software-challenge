import Lake
open Lean Lake DSL

package «software_challenge» where
  builtinLint := true
  fixedToolchain := true
  testDriver := "test_challenge"
  testDriverArgs := #["SoftwareChallengeTests", "SoftwareChallengeReadTests", "real_runs"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩,
    ⟨`linter.coreInternal, false⟩
  ]

@[default_target]
lean_lib «SoftwareChallenge» where
  globs := #[.andSubmodules `SoftwareChallenge]

lean_lib «SoftwareChallengeStatement» where
  roots := #[`SoftwareChallengeStatement.Challenge]
  leanOptions := #[⟨`warn.sorry, false⟩]

lean_lib «SoftwareChallengeTests» where
  roots := #[]
  globs := #[`Support, `Commands, `Complete, `Format, `Grade, `Graph, `Layering, `Match, `Steps].map
    (.one <| `SoftwareChallengeTests ++ ·) |>.push (.submodules `SoftwareChallengeTests.Rules)
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]

lean_lib «SoftwareChallengeFixtures» where
  roots := #[]
  globs := #[.submodules `SoftwareChallengeTests.Fixtures]
  precompileModules := true
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]

lean_lib «SoftwareChallengeReadTests» where
  needs := #[`@/SoftwareChallengeFixtures:leanArts]

lean_exe «grade» where
  root := `SoftwareChallenge.Steps.Grade

lean_exe «lsc-gate» where
  root := `SoftwareChallengeTests.Gate

def lineIn (file : System.FilePath) (holds : String → Bool) : IO Nat := do
  unless ← file.pathExists do return 1
  return ((((← IO.FS.readFile file).splitOn "\n").findIdx? holds).map (· + 1)).getD 1

def placeIn (pkg : Package) (holds : String → Bool) : IO Json := do
  return Json.mkObj [("file", pkg.relConfigFile.toString), ("line", ← lineIn pkg.configFile holds)]

def source (mod : Lake.Module) : Json :=
  Json.mkObj [("module", toJson mod.name), ("file", mod.relLeanFile.toString)]

def lexical (path : System.FilePath) : System.FilePath :=
  System.mkFilePath <| path.components.foldl (init := []) fun parts part =>
    if part == "." then parts else if part == ".." && parts.length > 1 then parts.dropLast else parts ++ [part]

partial def repositoryOf (dir : System.FilePath) : IO (Option System.FilePath) := do
  if ← (dir / ".git").pathExists then return some dir
  match dir.parent with
  | some parent => if parent == dir then return none else repositoryOf parent
  | none => return none

def ownTest (pkg : Package) (name : String) : IO (Option Json) := do
  let kind? := if pkg.scripts.contains name.toName then some ("script", "script ")
    else if (pkg.findLeanLib? name.toName).isSome then some ("library", "lean_lib ")
    else if (pkg.findLeanExe? name.toName).isSome then some ("executable", "lean_exe ") else none
  kind?.mapM fun (kind, keyword) => do
    let place ← placeIn pkg fun line => line.startsWith keyword &&
      ((line.drop keyword.length).toString.splitOn " ").head?.any ([name, s!"«{name}»"].contains ·)
    return Json.mkObj [("name", name), ("kind", kind), ("place", place)]

structure Prepared where
  text : String
  inputs : Array String
  challenge? : Option Lake.Module
  catalog : Array Lake.Module
  importers : Array Lake.Module

def prepare (pkg : Package) (testArgs : Array String) : FetchM Prepared := do
  let roots := (pkg.leanLibs.flatMap fun lib => lib.config.roots.filter (·.getString! == "Challenge")).toList.eraseDups
  let challenge? ← match roots with
    | [root] => (pkg.findModule? root).filterM (·.leanFile.pathExists)
    | _ => pure none
  let mut catalog := #[]
  for root in (← (← pkg.defaultModules.fetch).await) ++ challenge?.toArray do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || challenge?.any (·.name == mod.name) || catalog.any (·.name == mod.name) do
        catalog := catalog.push mod
  let closure ← challenge?.elim (pure #[]) fun challenge => do (← challenge.transImports.fetch).await
  let owned := catalog.filter fun mod => closure.any (·.name == mod.name) ||
    mod.name.components.any fun part => ["CoreSpec", "WorldSpec"].contains part.toString
  let configs ← #[pkg.relConfigFile.toString, pkg.relManifestFile.toString, "lean-toolchain"].filterM
    fun (file : String) => (pkg.dir / file).pathExists
  let inputs := (configs ++ (challenge?.toArray ++ owned).map (fun (mod : Lake.Module) => mod.relLeanFile.toString) ++
    #["owned.lock", "comparator.json"]).toList.eraseDups.toArray
  let importers ← challenge?.elim (pure #[]) fun challenge => catalog.filterM fun mod => do
    return (← (← mod.imports.fetch).await).any (·.name == challenge.name)
  let dir ← IO.FS.realPath pkg.dir
  let packages ← ((← getWorkspace).packages.filter (!·.isRoot)).mapM fun dep => do
    return Json.mkObj [("name", toJson dep.baseName), ("configured", (lexical (dir / dep.relDir)).toString),
      ("real", (← IO.FS.realPath dep.dir).toString), ("scope", dep.scope),
      ("manifestFile", dep.relManifestFile.toString), ("configFile", dep.relConfigFile.toString)]
  let builtinLint ← if pkg.config.builtinLint? == some true then placeIn pkg (·.contains "builtinLint")
    else pure Json.null
  let fields := [("packageDir", toJson dir.toString)] ++
    ((← repositoryOf dir).map fun repository => ("repository", toJson repository.toString)).toList ++ [
    ("configFiles", toJson configs), ("modules", toJson (catalog.map source)),
    ("challengeCandidates", toJson (roots.filterMap (pkg.findModule? · |>.map source))),
    ("exeRoots", toJson (pkg.leanExes.map (·.config.root))), ("packages", toJson packages),
    ("defaultTargets", toJson pkg.defaultTargets), ("builtinLint", builtinLint),
    ("lintDriver", toJson pkg.lintDriver), ("testDriver", toJson pkg.testDriver),
    ("testDriverArgs", toJson testArgs), ("testDriverArgsPlace", ← placeIn pkg (·.contains "testDriverArgs")),
    ("ownTests", toJson (← (testArgs.filterMapM (ownTest pkg) : IO (Array Json)))), ("inputs", toJson inputs)]
  return { text := (Json.mkObj fields).pretty, inputs, challenge?, catalog, importers }

def stepDir (pkg : Package) : System.FilePath := pkg.buildDir / "softwareChallenge"

def runner : System.FilePath := __dir__ / "SoftwareChallengeRun.lean"

def statusOf (pkg : Package) (step : String) : IO UInt32 := do
  let file := stepDir pkg / s!"{step}.status"
  unless ← file.pathExists do return 3
  return (((← IO.FS.readFile file).trimAscii.toString.toNat?).getD 3).toUInt32

def runStep (pkg : Package) (step : String) (args : Array String) : JobM (UInt32 × String) := do
  let status := stepDir pkg / s!"{step}.status"
  if ← status.pathExists then IO.FS.removeFile status
  let out ← IO.Process.output {
    cmd := (← getLean).toString
    args := #["--run", runner.toString, step, (stepDir pkg / "lake.json").toString] ++ args
    cwd := pkg.dir
    env := ← getAugmentedEnv }
  let code ← statusOf pkg step
  let missing := if code == 3 && !(← status.pathExists) then s!"\n`lean --run {runner} {step}` exited \
    {out.exitCode} without recording a result, so the step did not judge the package. Fix the errors above in the \
    library software_challenge, then run `lake build`." else ""
  return (code, out.stdout ++ out.stderr ++ missing)

def inputsTrace (pkg : Package) (prepared : Prepared) : JobM BuildTrace := do
  let files ← prepared.inputs.mapM fun (path : String) => do
    if ← (pkg.dir / path).pathExists then computeTrace (TextFilePath.mk (pkg.dir / path))
    else pure (BuildTrace.ofHash (pureHash path) s!"absent {path}")
  return mixTraceArray (files.push (.ofHash (pureHash prepared.text) "lake.json"))

def record (pkg : Package) (step : String) (prepared : Prepared) (args : Array String := #[]) : JobM Unit := do
  IO.FS.createDirAll (stepDir pkg)
  IO.FS.writeFile (stepDir pkg / s!"{step}.ran") ""
  IO.FS.writeFile (stepDir pkg / "lake.json") prepared.text
  addTrace (← computeTrace (TextFilePath.mk runner))
  let deps ← getTrace
  let before := mixTrace deps (← inputsTrace pkg prepared)
  setTrace before
  let traceFile := stepDir pkg / s!"{step}.trace"
  if ← (← readTraceFile traceFile).replayIfUpToDate (stepDir pkg / s!"{step}.status") before then return
  buildAction before traceFile do
    let (code, output) ← runStep pkg step args
    let shown := if step == "lint" then "\n" ++ output else output
    unless output.trimAscii.isEmpty do if code == 0 || code == 2 then logInfo shown else logError shown
  let after := mixTrace deps (← inputsTrace pkg prepared)
  if (← statusOf pkg step) == 3 then IO.FS.removeFile traceFile
  else if after.hash != before.hash then
    if let .ok data ← readTraceFile traceFile then
      BuildMetadata.writeFile traceFile { data with depHash := after.hash, log := {} }

def stepsJob : FetchM (Job Unit) := do
  let some steps ← findModule? `SoftwareChallenge.Steps | error "SoftwareChallenge.Steps is not in the workspace, so \
    no step can run. Add `require software_challenge from git \"https://github.com/vincentqb/lean-software-challenge\" \
    @ \"main\"` to lakefile.lean, run `lake update software_challenge`, then run `lake build`."
  return (← steps.leanArts.fetch).map fun _ => ()

def tolerated (job : Job Unit) : Job Bool := job.mapResult (sync := true) fun
  | .ok _ state => .ok true state
  | .error _ state => .ok false { state with log := {} }

package_facet softwareChallengeStatement pkg : Unit := do
  let prepared ← prepare pkg pkg.testDriverArgs
  let steps ← stepsJob
  unless prepared.importers.isEmpty do return ← steps.mapM fun _ => record pkg "importer" prepared #["statement"]
  let some challenge := prepared.challenge? | steps.mapM fun _ => record pkg "statement" prepared
  let built := tolerated ((← challenge.leanArts.fetch).map fun _ => ())
  (steps.zipWith (fun _ compiled => compiled) built).mapM fun compiled =>
    record pkg "statement" prepared (if compiled then #[] else #["failed"])

package_facet softwareChallenge pkg : Unit := do
  let prepared ← prepare pkg pkg.testDriverArgs
  let steps ← stepsJob
  unless prepared.importers.isEmpty do return ← steps.mapM fun _ => record pkg "importer" prepared #["lint"]
  let arts ← (prepared.catalog ++ prepared.challenge?.toArray).mapM fun mod => return (← mod.leanArts.fetch).map (fun _ => ())
  (steps.mix (Job.mixArray arts)).mapM fun _ => record pkg "lint" prepared

def lintTargets (prepared : Prepared) (pkg : Package) : FetchM (Job (Array String)) := do
  let imported ← prepared.catalog.foldlM (init := ({} : NameSet)) fun names mod => do
    return (← (← mod.transImports.fetch).await).foldl (·.insert ·.name) names
  let roots := pkg.leanExes.map (·.config.root)
  let tops := (prepared.catalog.filter (!imported.contains ·.name)).map (·.name)
  return Job.pure ((tops.filter (!roots.contains ·) ++ tops.filter roots.contains).map (·.toString))

def spawnStep (pkg : Package) (step : String) (testArgs : Array String) : ScriptM UInt32 := do
  let prepared ← runBuild do
    let prepared ← prepare pkg testArgs
    return (← stepsJob).map fun _ => prepared
  IO.FS.createDirAll (stepDir pkg)
  IO.FS.writeFile (stepDir pkg / "lake.json") prepared.text
  if ← (stepDir pkg / s!"{step}.status").pathExists then IO.FS.removeFile (stepDir pkg / s!"{step}.status")
  discard <| (← IO.Process.spawn {
    cmd := (← getLean).toString
    args := #["--run", runner.toString, step, (stepDir pkg / "lake.json").toString]
    cwd := pkg.dir
    env := ← getAugmentedEnv }).wait
  statusOf pkg step

script lint_challenge do
  let pkg ← getRootPackage
  let lake := (← getLake).toString
  let tops ← runBuild do lintTargets (← prepare pkg pkg.testDriverArgs) pkg
  let builtin ← IO.Process.output { cmd := lake, args := #["lint", "--builtin-only"] ++ tops, cwd := pkg.dir }
  let sections := (builtin.stdout.splitOn "\n-- ").zipIdx.filter fun (part, index) =>
    !(if index == 0 then part.startsWith "-- Text linter diagnostics" else part.startsWith "Text linter diagnostics")
  IO.print ("\n-- ".intercalate (sections.map (·.1)))
  IO.eprint builtin.stderr
  (← IO.getStdout).flush
  let failed := builtin.exitCode != 0 && (builtin.stderr.contains "error" ||
    sections.any fun (part, _) => part.startsWith "Found " || part.contains "error:")
  if ← (stepDir pkg / "lint.ran").pathExists then IO.FS.removeFile (stepDir pkg / "lint.ran")
  try discard <| runBuild (pkg.fetchFacetJob `softwareChallenge) catch _ => pure ()
  let ran ← (stepDir pkg / "lint.ran").pathExists
  let code ← if ran then statusOf pkg "lint" else pure 1
  unless ran do
    IO.eprintln "lake lint could not build the package's modules, as printed above, so the audit did not run. Fix \
      each error above; when the linker reports a `multiple definition`, two modules define the same name, or two \
      executables define `main`, so rename one of them. Then run `lake lint`."
  if failed then
    IO.eprintln "Lean's linters report the problems `lake lint --builtin-only` printed above, so the solution is not \
      clean. Fix each at the file and line it names, then run `lake lint`."
  return if failed && code != 3 then 1 else code

script test_challenge (args) do
  spawnStep (← getRootPackage) "test" args.toArray

script replay do
  spawnStep (← getRootPackage) "replay" (← getRootPackage).testDriverArgs

def gateRuns : Array (String × Name × List System.FilePath) := #[
  ("template", `templateRun, ["Examples" / "ConstantFolding"]),
  ("comparator", `comparatorRun, ["SoftwareChallengeTests" / "Comparator"]),
  ("grade", `gradeRun, ["Examples" / "ConstantFolding"])]

def gateRun (pkg : Package) (run : String) (dirs : List System.FilePath) : FetchM (Job Unit) := do
  let some gate := pkg.findLeanExe? `«lsc-gate» | error "lakefile.lean declares no lean_exe «lsc-gate»"
  let some grade := pkg.findLeanExe? `grade | error "lakefile.lean declares no lean_exe «grade»"
  let some library := pkg.findLeanLib? `SoftwareChallenge | error "lakefile.lean declares no lean_lib SoftwareChallenge"
  let deps := (← gate.exe.fetch).mix ((← grade.exe.fetch).mix ((← library.leanArts.fetch).mix (← stepsJob)))
  deps.mapM fun _ => do
    addLeanTrace
    for file in ["lakefile.lean", "lake-manifest.json", "lean-toolchain", runner.toString] do
      if ← (pkg.dir / file).pathExists then addTrace (← computeTrace (TextFilePath.mk (pkg.dir / file)))
    for dir in dirs do
      for file in ← (pkg.dir / dir).walkDir (enter := fun path => pure (path.fileName != some ".lake")) do
        unless (← file.isDir) || file.fileName == some "comparator.json" do
          addTrace (← computeTrace (TextFilePath.mk file))
    let log := pkg.buildDir / "gate" / s!"{run}.txt"
    buildUnlessUpToDate log (← getTrace) (log.addExtension "trace") do
      IO.FS.createDirAll (pkg.buildDir / "gate")
      let out ← IO.Process.output {
        cmd := gate.file.toString
        args := #[run]
        cwd := some pkg.dir
        env := #[("LAKE", some (← getLake).toString)] }
      IO.FS.writeFile log (out.stdout ++ out.stderr)
      unless out.exitCode == 0 do
        logError (out.stdout ++ out.stderr)
        error s!"`lake exe lsc-gate {run}` exited {out.exitCode}, so the {run} real run does not hold: fix each \
          failure above as it says, then run `lake build {run}Run`."
      logInfo out.stdout

target templateRun pkg : Unit := gateRun pkg "template" ["Examples" / "ConstantFolding"]

target comparatorRun pkg : Unit := gateRun pkg "comparator" ["SoftwareChallengeTests" / "Comparator"]

target gradeRun pkg : Unit := gateRun pkg "grade" ["Examples" / "ConstantFolding"]

script real_runs do
  let pkg ← getRootPackage
  let lake := (← getLake).toString
  let stale ← gateRuns.filterM fun (_, name, _) => do
    return (← IO.Process.output { cmd := lake, args := #["build", "--no-build", name.toString], cwd := pkg.dir }).exitCode != 0
  unless stale.isEmpty do
    IO.println s!"Real runs stale: {", ".intercalate (stale.map (·.2.1.toString)).toList}; `lake test -- full` runs them"
  return 0

script full do
  let pkg ← getRootPackage
  let start ← IO.monoMsNow
  for (run, _, _) in gateRuns do
    let trace := pkg.buildDir / "gate" / s!"{run}.txt.trace"
    if ← trace.pathExists then IO.FS.removeFile trace
  let code ← try runBuild (return Job.mixArray (← gateRuns.mapM fun (_, name, _) => pkg.fetchTargetJob name)); pure 0
    catch _ => pure 1
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"Real runs took {elapsed / 1000} s"
  if elapsed > 300000 then
    IO.eprintln s!"The real runs took {elapsed / 1000} s, over the 300 s that `lake test -- full` allows, so the full \
      gate fails. Find the slowest run in .lake/build/gate, make it faster, then run `lake test -- full`."
    return 1
  return code

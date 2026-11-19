import Lake
open Lean Lake DSL

package «software_challenge» where
  fixedToolchain := true
  lintDriver := "software_challenge/lint_challenge"
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
  globs := #[`Support, `Coverage, `Commands, `Complete, `Format, `Grade, `Graph, `Layering, `Match, `Steps, `Model,
    `Matrix, `Gate.Read].map (.one <| `SoftwareChallengeTests ++ ·) ++ #[.submodules `SoftwareChallengeTests.Rules,
      .submodules `SoftwareChallengeTests.Golden]
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]

lean_lib «SoftwareChallengeFixtures» where
  roots := #[]
  globs := #[.submodules `SoftwareChallengeTests.Fixtures]
  precompileModules := true
  leanOptions := #[⟨`linter.extra.unreachableTactic, false⟩]

lean_lib «SoftwareChallengeReadFixtures» where
  roots := #[]
  globs := #[.submodules `SoftwareChallengeReadTests.Fixtures]

lean_lib «SoftwareChallengeReadTests» where
  needs := #[`@/SoftwareChallengeFixtures:leanArts, `@/SoftwareChallengeReadFixtures:leanArts]

lean_exe «grade» where
  root := `SoftwareChallenge.Steps.Grade

lean_exe «lsc-gate» where
  root := `SoftwareChallengeTests.Gate

@[default_target]
target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())

def placeIn (pkg : Package) (holds : String → Bool) : IO Json := do
  let lines ← if ← pkg.configFile.pathExists then do pure ((← IO.FS.readFile pkg.configFile).splitOn "\n") else pure []
  let line := ((lines.findIdx? holds).map (· + 1)).getD 1
  return Json.mkObj [("file", pkg.relConfigFile.toString), ("line", toJson line)]

def source (mod : Lake.Module) : Json :=
  Json.mkObj [("module", toJson mod.name), ("file", mod.relLeanFile.toString)]

def lexical (path : System.FilePath) : System.FilePath :=
  System.mkFilePath <| path.components.foldl (init := []) fun parts part =>
    if part == "." then parts else if part == ".." && parts.length > 1 then parts.dropLast else parts ++ [part]

def ownTest (pkg : Package) (name : String) : IO (Option Json) := do
  let kind? := if pkg.scripts.contains name.toName then some ("script", "script ")
    else if (pkg.findLeanLib? name.toName).isSome then some ("library", "lean_lib ")
    else if (pkg.findLeanExe? name.toName).isSome then some ("executable", "lean_exe ") else none
  kind?.mapM fun (kind, keyword) => do
    let place ← placeIn pkg fun line => line.startsWith keyword &&
      ((line.drop keyword.length).toString.splitOn " ").head?.any ([name, s!"«{name}»"].contains ·)
    return Json.mkObj [("name", name), ("kind", kind), ("place", place)]

def overriddenPackages (file : System.FilePath) : IO (Array String) := do
  unless ← file.pathExists do return #[]
  let entries := ((Json.parse (← IO.FS.readFile file)).bind (·.getObjValAs? (Array Json) "packages")).toOption.getD #[]
  return entries.filterMap fun entry => (entry.getObjValAs? String "name").toOption

structure Prepared where
  text : String
  inputs : Array String
  challenge? : Option Lake.Module
  catalog : Array Lake.Module
  owned : Array Lake.Module
  importers : Array Lake.Module
  lintTargets : Array String

def prepare (pkg : Package) (testArgs : Array String) : FetchM Prepared := do
  let roots := (pkg.leanLibs.flatMap fun lib => lib.config.roots.filter (·.getString! == "Challenge")).toList.eraseDups
  let challenge? ← match roots with
    | [root] => (pkg.findModule? root).filterM (·.leanFile.pathExists)
    | _ => pure none
  let mut catalog := #[]
  for root in (← (← pkg.defaultModules.fetch).await) ++ challenge?.toArray do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || (challenge?.toArray ++ catalog).any (·.name == mod.name) do
        catalog := catalog.push mod
  let imports ← catalog.mapM fun mod => return (mod, ← (← mod.transImports.fetch).await)
  let closure ← challenge?.elim (pure #[]) fun challenge => do (← challenge.transImports.fetch).await
  let owned := catalog.filter fun mod => closure.any (·.name == mod.name) ||
    mod.name.components.any fun part => ["CoreSpec", "WorldSpec"].contains part.toString
  let configs ← #[pkg.relConfigFile.toString, pkg.relManifestFile.toString, "lean-toolchain"].filterM
    fun (file : String) => (pkg.dir / file).pathExists
  let inputs := (configs ++ (challenge?.toArray ++ owned).map (fun (mod : Lake.Module) => mod.relLeanFile.toString)
    ++ #["owned.lock", "comparator.json"]).toList.eraseDups.toArray
  let importers ← challenge?.elim (pure #[]) fun challenge => catalog.filterM fun mod => do
    return (← (← mod.imports.fetch).await).any (·.name == challenge.name)
  let tops := catalog.filter fun mod => !imports.any (·.2.any (·.name == mod.name))
  let exeRoots := pkg.leanExes.map (·.config.root)
  let dir ← IO.FS.realPath pkg.dir
  let overridden ← overriddenPackages (← getWorkspace).packageOverridesFile
  let packages ← ((← getWorkspace).packages.filter (!·.isRoot)).mapM fun dep => do
    return Json.mkObj [("name", toJson dep.baseName), ("configured", (lexical (dir / dep.relDir)).toString),
      ("real", (← IO.FS.realPath dep.dir).toString), ("overridden", toJson (overridden.contains dep.baseName.toString)),
      ("scope", dep.scope), ("manifestFile", dep.relManifestFile.toString), ("configFile", dep.relConfigFile.toString)]
  let fields := [("packageDir", toJson dir.toString), ("configFiles", toJson configs),
    ("modules", toJson (catalog.map source)),
    ("challengeCandidates", toJson (roots.filterMap (pkg.findModule? · |>.map source))),
    ("exeRoots", toJson exeRoots), ("packages", toJson packages), ("defaultTargets", toJson pkg.defaultTargets),
    ("builtinLint", ← if pkg.config.builtinLint? == some true then placeIn pkg (·.contains "builtinLint")
      else pure Json.null),
    ("lintDriver", toJson pkg.lintDriver), ("testDriver", toJson pkg.testDriver),
    ("testDriverArgs", toJson testArgs),
    ("testDriverArgsPlace", ← placeIn pkg (·.contains "testDriverArgs")),
    ("ownTests", toJson (← (testArgs.filterMapM (ownTest pkg) : IO (Array Json)))), ("inputs", toJson inputs)]
  return { text := (Json.mkObj fields).pretty, inputs, challenge?, catalog, owned, importers
           lintTargets := ((tops.filter (!exeRoots.contains ·.name)) ++ tops.filter (exeRoots.contains ·.name)).map
             (·.name.toString) }

def stepDir (pkg : Package) : System.FilePath := pkg.buildDir / "softwareChallenge"

def runner : System.FilePath := __dir__ / "SoftwareChallengeRun.lean"

def statusOf (pkg : Package) (step : String) : IO UInt32 := do
  let file := stepDir pkg / s!"{step}.status"
  unless ← file.pathExists do return 3
  return (((← IO.FS.readFile file).trimAscii.toString.toNat?).getD 3).toUInt32

def stepArgs (pkg : Package) (prepared : Prepared) (step : String) (args : Array String) : IO (Array String) := do
  IO.FS.createDirAll (stepDir pkg)
  IO.FS.writeFile (stepDir pkg / "lake.json") prepared.text
  if ← (stepDir pkg / s!"{step}.status").pathExists then IO.FS.removeFile (stepDir pkg / s!"{step}.status")
  return #["--run", runner.toString, step, (stepDir pkg / "lake.json").toString] ++ args

def inputsTrace (pkg : Package) (prepared : Prepared) : JobM BuildTrace := do
  let files ← (prepared.inputs ++ prepared.importers.map (·.relLeanFile.toString)).mapM fun (path : String) => do
    if ← (pkg.dir / path).pathExists then computeTrace (TextFilePath.mk (pkg.dir / path))
    else pure (BuildTrace.ofHash (pureHash path) s!"absent {path}")
  return mixTraceArray (files.push (.ofHash (pureHash prepared.text) "lake.json"))

def record (pkg : Package) (step : String) (prepared : Prepared) (args : JobM (Array String) := pure #[]) :
    JobM Unit := do
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
    let stepped ← stepArgs pkg prepared step (← args)
    let lean := (← getLean).toString
    let out ← IO.Process.output { cmd := lean, args := stepped, cwd := pkg.dir, env := ← getAugmentedEnv }
    let code ← statusOf pkg step
    let judged := (← (stepDir pkg / s!"{step}.status").pathExists) && (code == 0 || code == 2 ||
      !(out.stdout ++ out.stderr).trimAscii.isEmpty)
    let shown := out.stdout ++ out.stderr ++ if judged then "" else s!"\n`lean --run {runner} {step}` exited \
      {out.exitCode} without a verdict, so the step did not judge the package. Fix the errors above in \
      software_challenge, then run `{if step == "lint" then "lake lint" else "lake build"}`."
    IO.FS.writeFile (stepDir pkg / s!"{step}.out") shown
    unless shown.trimAscii.isEmpty do
      if code == 0 || code == 2 then logInfo ((if step == "lint" then "\n" else "") ++ shown) else logError shown
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

def compiled (pkg : Package) (challenge : Lake.Module) : JobM (Array String) := do
  let dir := stepDir pkg / "statement"
  let olean := modToFilePath dir challenge.name "olean"
  IO.FS.createDirAll (olean.parent.getD dir)
  let out ← IO.Process.output { cmd := (← getLean).toString, cwd := pkg.dir, env := ← getAugmentedEnv
                                args := #[challenge.leanFile.toString, "-o", olean.toString] ++
                                  challenge.leanOptions.values.foldl (fun args name value =>
                                    args.push s!"-D{name}={value.asCliFlagValue}") #[] }
  if out.exitCode == 0 then return #[dir.toString]
  logError (out.stdout ++ out.stderr)
  return #["failed"]

package_facet softwareChallengeStatement pkg : Unit := do
  let prepared ← prepare pkg pkg.testDriverArgs
  let steps ← stepsJob
  unless prepared.importers.isEmpty do
    return ← steps.mapM fun _ => record pkg "statement" prepared (pure #["importers"])
  let some challenge := prepared.challenge? | steps.mapM fun _ => record pkg "statement" prepared
  let arts ← ((← (← challenge.imports.fetch).await) ++ prepared.owned).mapM fun mod => do
    return (← mod.leanArts.fetch).map fun _ => ()
  (steps.mix (Job.mixArray arts)).mapM fun _ => record pkg "statement" prepared (compiled pkg challenge)

package_facet softwareChallenge pkg : Unit := do
  let prepared ← prepare pkg pkg.testDriverArgs
  let steps ← stepsJob
  unless prepared.importers.isEmpty do
    return ← steps.mapM fun _ => record pkg "lint" prepared (pure #["importers"])
  let arts ← (prepared.catalog ++ prepared.challenge?.toArray).mapM fun mod => do
    return (← mod.leanArts.fetch).map fun _ => ()
  (steps.mix (Job.mixArray arts)).mapM fun _ => record pkg "lint" prepared

def spawnStep (step : String) (testArgs : Array String) (args : Prepared → Array String := fun _ => #[]) :
    ScriptM UInt32 := do
  let pkg ← getRootPackage
  let prepared ← runBuild do
    let prepared ← prepare pkg testArgs
    return (← stepsJob).map fun _ => prepared
  discard <| (← IO.Process.spawn {
    cmd := (← getLean).toString, args := ← stepArgs pkg prepared step (args prepared), cwd := pkg.dir
    env := ← getAugmentedEnv }).wait
  statusOf pkg step

script lint_challenge do
  spawnStep "drive" (← getRootPackage).testDriverArgs (·.lintTargets)

script test_challenge (args) do
  spawnStep "test" args.toArray

script replay do
  spawnStep "replay" (← getRootPackage).testDriverArgs

def gateInputs : String → List System.FilePath
  | "comparator" => ["SoftwareChallengeTests" / "Comparator"]
  | _ => ["Examples" / "ConstantFolding"]

def gateRun (pkg : Package) (run : String) : FetchM (Job Unit) := do
  let (some gate, some grade, some library) := (pkg.findLeanExe? `«lsc-gate», pkg.findLeanExe? `grade,
    pkg.findLeanLib? `SoftwareChallenge) | error s!"lakefile.lean declares no lean_exe «lsc-gate», lean_exe «grade» \
      or lean_lib «SoftwareChallenge», so no real run can start. Restore them, then run `lake build {run}Run`."
  let inputs ← (gateInputs run).toArray.mapM fun dir => return (← inputDir (pkg.dir / dir) true fun path =>
    !path.components.contains ".lake" && path.fileName != some "comparator.json").map fun _ => ()
  let read ← #[`SoftwareChallengeTests.Model, `SoftwareChallengeTests.Golden.ConstantFolding].mapM fun name => do
    let some mod ← findModule? name | error s!"{name} is not in the workspace, so the real run's reader cannot \
      start. Restore it in lean_lib «SoftwareChallengeTests», then run `lake build {run}Run`."
    return (← mod.leanArts.fetch).map fun _ => ()
  let deps := #[(← gate.exe.fetch).map (fun _ => ()), (← grade.exe.fetch).map (fun _ => ()),
    (← library.leanArts.fetch).map (fun _ => ()), ← stepsJob] ++ read ++ inputs
  (Job.mixArray deps).mapM fun _ => do
    addLeanTrace
    for file in ["lakefile.lean", "lake-manifest.json", "lean-toolchain", runner.toString,
        "SoftwareChallengeTests/Gate/Read.lean"] do
      addTrace (← computeTrace (TextFilePath.mk (pkg.dir / file)))
    let log := pkg.buildDir / "gate" / s!"{run}.txt"
    buildUnlessUpToDate log (← getTrace) (log.addExtension "trace") do
      IO.FS.createDirAll (pkg.buildDir / "gate")
      let out ← IO.Process.output {
        cmd := gate.file.toString, args := #[run], cwd := some pkg.dir, env := #[("LAKE", some (← getLake).toString)] }
      IO.FS.writeFile log (out.stdout ++ out.stderr)
      if out.exitCode == 0 then logInfo out.stdout else logError (out.stdout ++ out.stderr)

target templateRun pkg : Unit := gateRun pkg "template"

target comparatorRun pkg : Unit := gateRun pkg "comparator"

target gradeRun pkg : Unit := gateRun pkg "grade"

def gateScript (mode : String) : ScriptM UInt32 := do
  let pkg ← getRootPackage
  let some gate := pkg.findLeanExe? `«lsc-gate» | return 1
  let exe ← runBuild gate.exe.fetch
  (← IO.Process.spawn {
    cmd := exe.toString, args := #[mode], cwd := pkg.dir, env := #[("LAKE", some (← getLake).toString)] }).wait

script real_runs do gateScript "stale"

script full do gateScript "full"

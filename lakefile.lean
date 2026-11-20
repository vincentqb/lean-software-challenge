import Lake
open Lean Lake DSL

package «software_challenge» where
  fixedToolchain := true
  lintDriver := "software_challenge/lint_challenge"
  testDriver := "software_challenge/test_challenge"
  testDriverArgs := #["SoftwareChallengeTests", "SoftwareChallengeReadTests", "real_runs"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.all, true⟩, ⟨`linter.missingDocs, false⟩]

@[default_target]
lean_lib «SoftwareChallenge» where globs := #[.andSubmodules `SoftwareChallenge]

lean_lib «SoftwareChallengeStatement» where
  roots := #[`SoftwareChallengeStatement.Challenge]
  leanOptions := #[⟨`warn.sorry, false⟩]

lean_lib «SoftwareChallengeTests» where
  roots := #[]
  globs := #[`Support, `Coverage, `Commands, `Complete, `Format, `Grade, `Graph, `Layering, `Match, `Steps,
    `Gate.Read].map (.one <| `SoftwareChallengeTests ++ ·) ++ #[.submodules `SoftwareChallengeTests.Rules,
      .submodules `SoftwareChallengeTests.Golden]

lean_lib «SoftwareChallengeFixtures» where
  roots := #[]
  globs := #[.submodules `SoftwareChallengeTests.Fixtures]
  precompileModules := true

lean_lib «SoftwareChallengeReadFixtures» where
  roots := #[]
  globs := #[.submodules `SoftwareChallengeReadTests.Fixtures]

lean_lib «SoftwareChallengeReadTests» where
  needs := #[`@/SoftwareChallengeFixtures:leanArts, `@/SoftwareChallengeReadFixtures:leanArts]

lean_exe «grade» where root := `SoftwareChallenge.Steps.Grade

lean_exe «lsc-gate» where root := `SoftwareChallengeTests.Gate

@[default_target]
target statement pkg : Unit := do return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())

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

def prepare (pkg : Package) (testArgs : Array String) : FetchM Prepared := do
  let candidates := (pkg.leanLibs.flatMap (·.config.roots.filter (·.getString! == "Challenge"))).toList.eraseDups
  let challenge? ← if let [root] := candidates then (pkg.findModule? root).filterM (·.leanFile.pathExists)
    else pure none
  let exeRoots := (pkg.leanExes.filter (pkg.defaultTargets.contains ·.name)).map (·.config.root)
  let mut catalog := #[]
  for root in (← (← pkg.defaultModules.fetch).await) ++ exeRoots.filterMap pkg.findModule? ++ challenge?.toArray do
    for mod in (← (← root.transImports.fetch).await).push root do
      unless mod.pkg.keyName != pkg.keyName || (challenge?.toArray ++ catalog).any (·.name == mod.name) do
        catalog := catalog.push mod
  let closure ← challenge?.elim (pure #[]) fun challenge => do (← challenge.transImports.fetch).await
  let owned := catalog.filter fun mod => closure.any (·.name == mod.name) ||
    mod.name.components.any fun part => ["CoreSpec", "WorldSpec"].contains part.toString
  let importers ← challenge?.elim (pure #[]) fun challenge => catalog.filterM fun mod => do
    return (← (← mod.imports.fetch).await).any (·.name == challenge.name)
  let configs ← #[pkg.relConfigFile.toString, pkg.relManifestFile.toString, "lean-toolchain"].filterM
    fun (file : String) => (pkg.dir / file).pathExists
  let inputs := (configs ++ (challenge?.toArray ++ owned).map (·.relLeanFile.toString) ++
    #["owned.lock", "comparator.json"]).toList.eraseDups.toArray
  let dir ← IO.FS.realPath pkg.dir
  let overridden ← overriddenPackages (← getWorkspace).packageOverridesFile
  let packages ← ((← getWorkspace).packages.filter (!·.isRoot)).mapM fun dep => do
    return Json.mkObj [("name", toJson dep.baseName), ("configured", (dir / dep.relDir).toString),
      ("real", (← IO.FS.realPath dep.dir).toString), ("overridden", overridden.contains dep.baseName.toString),
      ("scope", dep.scope), ("manifestFile", dep.relManifestFile.toString),
      ("configFile", dep.relConfigFile.toString)]
  let source := fun (mod : Lake.Module) => Json.mkObj [("module", toJson mod.name), ("file", mod.relLeanFile.toString)]
  let kinds : List (String × (Name → Bool)) := [("script", pkg.scripts.contains),
    ("library", fun name => (pkg.findLeanLib? name).isSome), ("executable", fun name => (pkg.findLeanExe? name).isSome)]
  let ownTests := testArgs.filterMap fun test => (kinds.find? (·.2 test.toName)).map fun (kind, _) =>
    Json.mkObj [("name", test), ("kind", kind)]
  let text := Json.pretty <| Json.mkObj [("packageDir", dir.toString), ("configFiles", toJson configs),
    ("modules", toJson (catalog.map source)), ("defaultExeRoots", toJson exeRoots), ("packages", toJson packages),
    ("challengeCandidates", toJson (candidates.filterMap (pkg.findModule? · |>.map source))),
    ("defaultTargets", toJson pkg.defaultTargets), ("builtinLint", pkg.config.builtinLint? == some true),
    ("lintDriver", pkg.lintDriver), ("testDriver", pkg.testDriver), ("testDriverArgs", toJson testArgs),
    ("ownTests", toJson ownTests), ("inputs", toJson inputs)]
  return { text, inputs, challenge?, catalog, owned, importers }

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

def record (pkg : Package) (step : String) (prepared : Prepared) (args : Array String) : JobM Unit := do
  IO.FS.createDirAll (stepDir pkg)
  IO.FS.writeFile (stepDir pkg / s!"{step}.ran") ""
  IO.FS.writeFile (stepDir pkg / "lake.json") prepared.text
  addTrace (← computeTrace (TextFilePath.mk runner))
  let deps ← getTrace
  let before := mixTrace deps (← inputsTrace pkg prepared)
  setTrace before
  let traceFile := stepDir pkg / s!"{step}.trace"
  buildUnlessUpToDate (stepDir pkg / s!"{step}.status") before traceFile do
    let out ← IO.Process.output { cmd := (← getLean).toString, args := ← stepArgs pkg prepared step args, cwd := pkg.dir
                                  env := ← getAugmentedEnv }
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
    no step can run. Require software_challenge in lakefile.lean, then run `lake build`."
  return (← steps.leanArts.fetch).map fun _ => ()

def stepJob (pkg : Package) (step : String) (prepared : Prepared) (mods : Array Lake.Module) (args : Array String) :
    FetchM (Job Unit) := do
  let (mods, args) := if prepared.importers.isEmpty then (mods, args) else (#[], #["importers"])
  let arts ← mods.mapM fun mod => return (← mod.leanArts.fetch).map fun _ => ()
  ((← stepsJob).mix (Job.mixArray arts)).mapM fun _ => record pkg step prepared args

package_facet softwareChallengeStatement pkg : Unit := do
  let prepared ← prepare pkg pkg.testDriverArgs
  let some challenge := prepared.challenge? | stepJob pkg "statement" prepared #[] #[]
  stepJob pkg "statement" prepared ((← (← challenge.imports.fetch).await) ++ prepared.owned) <|
    challenge.leanOptions.values.foldl (fun args name value => args.push s!"-D{name}={value.asCliFlagValue}") #[]

package_facet softwareChallenge pkg : Unit := do
  let prepared ← prepare pkg pkg.testDriverArgs
  stepJob pkg "lint" prepared (prepared.catalog ++ prepared.challenge?.toArray) #[]

def spawnStep (step : String) (testArgs : Array String) (args : Array String := #[]) : ScriptM UInt32 := do
  let pkg ← getRootPackage
  let prepared ← runBuild do
    let prepared ← prepare pkg testArgs
    return (← stepsJob).map fun _ => prepared
  discard <| (← IO.Process.spawn { cmd := (← getLean).toString, args := ← stepArgs pkg prepared step args, cwd := pkg.dir
                                   env := ← getAugmentedEnv }).wait
  statusOf pkg step

script lint_challenge do spawnStep "drive" (← getRootPackage).testDriverArgs

def loadDynlibs (pkg : Package) : FetchM (Job (Array String)) := do
  return (Job.collectArray (← pkg.externLibs.mapM (·.dynlib.fetch))).map (·.map (s!"--load-dynlib={·.path}"))

script test_challenge (args) do
  let loads ← runBuild (loadDynlibs (← getRootPackage))
  spawnStep "test" args.toArray loads

script replay do spawnStep "replay" (← getRootPackage).testDriverArgs

def gateRun (pkg : Package) (run : String) (dir : System.FilePath) : FetchM (Job Unit) := do
  let some read ← findModule? `SoftwareChallengeTests.Gate.Read | error "SoftwareChallengeTests.Gate.Read is missing"
  let files ← inputDir (pkg.dir / dir) true fun path =>
    !path.components.contains ".lake" && path.fileName != some "comparator.json"
  let deps := (((← «lsc-gate».fetch).mix (← grade.fetch)).mix ((← «SoftwareChallenge».fetch).mix files)).mix
    (← read.leanArts.fetch)
  deps.mapM fun _ => do
    addLeanTrace
    for file in [pkg.configFile, pkg.manifestFile, pkg.dir / "lean-toolchain", runner] do
      addTrace (← computeTrace (TextFilePath.mk file))
    let log := pkg.buildDir / "gate" / s!"{run}.txt"
    buildUnlessUpToDate log (← getTrace) (log.addExtension "trace") do
      IO.FS.createDirAll (pkg.buildDir / "gate")
      let out ← IO.Process.output { cmd := (← «lsc-gate».get).file.toString, args := #[run], cwd := pkg.dir
                                    env := #[("LAKE", (← getLake).toString)] }
      IO.FS.writeFile log (out.stdout ++ out.stderr)
      if out.exitCode == 0 then logInfo out.stdout else logError (out.stdout ++ out.stderr)

target templateRun pkg : Unit := gateRun pkg "template" ("Examples" / "ConstantFolding")

target comparatorRun pkg : Unit := gateRun pkg "comparator" ("SoftwareChallengeTests" / "Comparator")

target gradeRun pkg : Unit := gateRun pkg "grade" ("Examples" / "ConstantFolding")

target nativeRun pkg : Unit := gateRun pkg "native" ("SoftwareChallengeTests" / "Native")

def gate (mode : String) : ScriptM UInt32 := do
  (← IO.Process.spawn { cmd := (← runBuild «lsc-gate».fetch).toString, args := #[mode], cwd := (← getRootPackage).dir
                        env := #[("LAKE", (← getLake).toString)] }).wait

script real_runs do gate "stale"

script full do gate "full"

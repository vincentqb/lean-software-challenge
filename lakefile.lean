import Lake
import Lake.Load.Manifest
open Lean Lake DSL

package «software_challenge» where
  testDriver := "test"
  builtinLint := true
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.all, true⟩, ⟨`linter.missingDocs, false⟩]

@[default_target]
lean_lib «SoftwareChallenge» where
  roots := #[`SoftwareChallenge, `SoftwareChallengeRun]
  globs := #[.andSubmodules `SoftwareChallenge, .one `SoftwareChallengeRun]

@[default_target]
lean_exe «grade» where root := `SoftwareChallenge.Grade

lean_lib «SoftwareChallengeTests» where globs := #[.andSubmodules `SoftwareChallengeTests]

def runner : System.FilePath := __dir__ / "SoftwareChallengeRun.lean"

def stepDir (pkg : Package) : System.FilePath := pkg.buildDir / "softwareChallenge"

def rootNamed (pkg : Package) (last next : String) : FetchM Lake.Module := do
  let found := (pkg.leanLibs.flatMap (·.config.roots)).filter (·.getString! == last)
  let some mod := found[0]?.bind pkg.findModule? | error s!"{pkg.relConfigFile}: no lean_lib of {pkg.baseName} has a \
    root module named {last}, so `{next}` has no {last} to judge. Add one to the roots of a lean_lib, as \
    Examples/ConstantFolding does, then run `{next}`."
  return mod

def packageClosure (pkg : Package) (roots : Array Lake.Module) : FetchM (Array Lake.Module) := do
  let mut found := #[]
  for root in roots do
    for mod in (← (← root.transImports.fetch).await).push root do
      if mod.pkg.keyName == pkg.keyName && !found.any (·.name == mod.name) then found := found.push mod
  return found

def planOf (pkg : Package) (challenge : Lake.Module) (solution : Name) (modules : Array Lake.Module)
    (programs : Array Name) (tests : Option Name) : FetchM Json := do
  let source := fun (mod : Lake.Module) => Json.mkObj [("module", toJson mod.name), ("file", mod.relLeanFile.toString)]
  let overridden ← Manifest.tryLoadEntries (← getWorkspace).packageOverridesFile
  let packages ← ((← getWorkspace).packages.filter (!·.isRoot)).mapM fun dep => do
    return Json.mkObj [("name", toJson dep.baseName), ("real", (← IO.FS.realPath dep.dir).toString),
      ("overridden", overridden.any (·.name == dep.baseName)), ("scope", dep.scope),
      ("manifestFile", dep.relManifestFile.toString), ("configFile", dep.relConfigFile.toString)]
  return Json.mkObj [("packageDir", (← IO.FS.realPath pkg.dir).toString), ("challenge", source challenge),
    ("solution", toJson solution), ("modules", toJson (modules.map source)),
    ("programs", toJson programs), ("tests", toJson tests), ("packages", toJson packages)]

def stepsJob : FetchM (Job Unit) := do
  let some steps ← findModule? `SoftwareChallenge.Steps | error "SoftwareChallenge.Steps is not in the workspace, \
    so no step can run. Require software_challenge in lakefile.lean, then run `lake build`."
  return (← steps.irArts.fetch).map fun _ => ()

def stepProcess (pkg : Package) (step : String) (plan : Json) (lean : System.FilePath)
    (env : Array (String × Option String)) : IO IO.Process.SpawnArgs := do
  IO.FS.createDirAll (stepDir pkg)
  IO.FS.writeFile (stepDir pkg / s!"{step}.json") plan.pretty
  return { cmd := lean.toString, args := #["--run", runner.toString, step, (stepDir pkg / s!"{step}.json").toString]
           cwd := pkg.dir, env }

package_facet softwareChallengeStatement pkg : Unit := do
  let challenge ← rootNamed pkg "Challenge" "lake build"
  let solution := ((pkg.leanLibs.flatMap (·.config.roots)).find? (·.getString! == "Solution")).getD `Solution
  let owned ← packageClosure pkg #[challenge]
  let plan ← planOf pkg challenge solution owned #[] none
  ((← challenge.olean.fetch).mix (← stepsJob)).mapM fun _ => do
    addPureTrace plan.compress "plan"
    for file in owned.map (·.leanFile) |>.push runner do addTrace (← computeTrace (TextFilePath.mk file))
    buildUnlessUpToDate (pkg.dir / "comparator.json") (← getTrace) (stepDir pkg / "statement.trace") do
      let out ← IO.Process.output (← stepProcess pkg "statement" plan (← getLean) (← getAugmentedEnv))
      unless out.exitCode == 0 do error (out.stdout ++ out.stderr)
      unless (out.stdout ++ out.stderr).trimAscii.isEmpty do logInfo (out.stdout ++ out.stderr)

def testDriverOf (pkg : Package) : Option Name :=
  match pkg.testDriver.splitOn "/" with
  | [name] => some name.toName
  | [owner, name] => if owner.toName == pkg.baseName then some name.toName else none
  | _ => none

script lint do
  let pkg ← getRootPackage
  let plan ← runBuild do
    let challenge ← rootNamed pkg "Challenge" "lake lint"
    let solution ← rootNamed pkg "Solution" "lake lint"
    let tests := pkg.leanExes.filter (some ·.name == testDriverOf pkg)
    let programs := pkg.leanExes.filter fun exe => pkg.defaultTargets.contains exe.name && !tests.any (·.name == exe.name)
    let roots := #[challenge, solution] ++ (programs ++ tests).map (·.root)
    let plan ← planOf pkg challenge solution.name (← packageClosure pkg roots) (programs.map (·.root.name))
      (tests[0]?.map (·.root.name))
    let built ← roots.mapM fun mod => return (← mod.olean.fetch).map fun _ => ()
    return ((← stepsJob).mix (Job.mixArray built)).map fun _ => plan
  let code ← (← IO.Process.spawn (← stepProcess pkg "lint" plan (← getLean) (← getAugmentedEnv))).wait
  unless code == 2 && pkg.config.builtinLint? == some true do return code
  let builtin ← IO.Process.output { cmd := (← getLake).toString, args := #["lint", "--builtin-only"], cwd := pkg.dir }
  return if builtin.exitCode == 0 then code else 1

script test do
  let pkg ← getRootPackage
  runBuild do
    let some suite ← findModule? `SoftwareChallengeTests.Suite | error "SoftwareChallengeTests.Suite is missing"
    let some run ← findModule? `SoftwareChallengeRun | error "SoftwareChallengeRun is missing"
    let linked ← #[`SoftwareChallenge, `SoftwareChallenge.Attributes, `SoftwareChallenge.Tests].filterMapM findModule?
    let objects ← linked.mapM fun mod => return (← mod.o.fetch).map fun _ => ()
    return ((((← suite.irArts.fetch).mix (← run.irArts.fetch)).mix (← stepsJob)).mix ((← grade.fetch).map fun _ => ())).mix
      (Job.mixArray objects)
  (← IO.Process.spawn { cmd := (← getLean).toString, args := #["--run", (pkg.dir / "SoftwareChallengeTests.lean").toString]
                        cwd := pkg.dir, env := ← getAugmentedEnv }).wait

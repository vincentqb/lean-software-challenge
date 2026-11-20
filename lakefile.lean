import Lake
import Lake.Load.Manifest
open Lean Lake DSL

package «software_challenge» where
  builtinLint := true
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.all, true⟩, ⟨`linter.missingDocs, false⟩]

@[default_target]
lean_lib «SoftwareChallenge» where
  roots := #[`SoftwareChallenge, `SoftwareChallengeRun]
  globs := #[.andSubmodules `SoftwareChallenge, .one `SoftwareChallengeRun]

@[default_target]
lean_exe «grade» where root := `SoftwareChallenge.Grade

def runner : System.FilePath := __dir__ / "SoftwareChallengeRun.lean"

def stepDir (pkg : Package) : System.FilePath := pkg.buildDir / "softwareChallenge"

def rootNamed (pkg : Package) (last : String) : FetchM Lake.Module := do
  let found := (pkg.leanLibs.flatMap (·.config.roots)).filter (·.getString! == last)
  let some name := found[0]? | error s!"{pkg.relConfigFile}: no lean_lib of {pkg.baseName} has a root module named \
    {last}, so there is no challenge to judge. Add one, as Examples/ConstantFolding does, then run `lake build`."
  let some mod := pkg.findModule? name | error s!"{pkg.relConfigFile}: {name} is a root module no lean_lib builds"
  return mod

def packageClosure (pkg : Package) (roots : Array Lake.Module) : FetchM (Array Lake.Module) := do
  let mut found := #[]
  for root in roots do
    for mod in (← (← root.transImports.fetch).await).push root do
      if mod.pkg.keyName == pkg.keyName && !found.any (·.name == mod.name) then found := found.push mod
  return found

def planOf (pkg : Package) (challenge : Lake.Module) (solution : Name) (roots : Array Lake.Module)
    (programs : Array Name) (tests : Option Name) : FetchM Json := do
  let source := fun (mod : Lake.Module) => Json.mkObj [("module", toJson mod.name), ("file", mod.relLeanFile.toString)]
  let overridden ← Manifest.tryLoadEntries (← getWorkspace).packageOverridesFile
  let packages ← ((← getWorkspace).packages.filter (!·.isRoot)).mapM fun dep => do
    return Json.mkObj [("name", toJson dep.baseName), ("real", (← IO.FS.realPath dep.dir).toString),
      ("overridden", overridden.any (·.name == dep.baseName)), ("scope", dep.scope),
      ("manifestFile", dep.relManifestFile.toString), ("configFile", dep.relConfigFile.toString)]
  return Json.mkObj [("packageDir", (← IO.FS.realPath pkg.dir).toString), ("challenge", source challenge),
    ("solution", toJson solution), ("modules", toJson ((← packageClosure pkg (roots.push challenge)).map source)),
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
  let challenge ← rootNamed pkg "Challenge"
  let solution := ((pkg.leanLibs.flatMap (·.config.roots)).find? (·.getString! == "Solution")).getD `Solution
  let plan ← planOf pkg challenge solution #[] #[] none
  ((← challenge.olean.fetch).mix (← stepsJob)).mapM fun _ => do
    addPureTrace plan.compress "plan"
    addTrace (← computeTrace (TextFilePath.mk runner))
    buildUnlessUpToDate (pkg.dir / "comparator.json") (← getTrace) (stepDir pkg / "statement.trace") do
      let out ← IO.Process.output (← stepProcess pkg "statement" plan (← getLean) (← getAugmentedEnv))
      unless out.exitCode == 0 do error (out.stdout ++ out.stderr)
      unless (out.stdout ++ out.stderr).trimAscii.isEmpty do logInfo (out.stdout ++ out.stderr)

script lint do
  let pkg ← getRootPackage
  let plan ← runBuild do
    let challenge ← rootNamed pkg "Challenge"
    let solution ← rootNamed pkg "Solution"
    let tests := pkg.leanExes.filter (·.name.toString == pkg.testDriver)
    let programs := pkg.leanExes.filter fun exe => pkg.defaultTargets.contains exe.name && !tests.any (·.name == exe.name)
    let roots := #[solution] ++ (programs ++ tests).filterMap (pkg.findModule? ·.config.root)
    let plan ← planOf pkg challenge solution.name roots (programs.map (·.config.root)) (tests[0]?.map (·.config.root))
    let built ← (roots.push challenge).mapM fun mod => return (← mod.olean.fetch).map fun _ => ()
    return ((← stepsJob).mix (Job.mixArray built)).map fun _ => plan
  (← IO.Process.spawn (← stepProcess pkg "lint" plan (← getLean) (← getAugmentedEnv))).wait

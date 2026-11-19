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

def challengeUndeclared : String :=
  "lakefile.lean declares no lean_lib «Challenge», so Challenge.lean, which states the challenge, is not part of the \
    package. Add the line ``lean_lib «Challenge» where leanOptions := #[⟨`warn.sorry, false⟩]`` to lakefile.lean, \
    create Challenge.lean if it is missing, delete owned.lock if there is one, then run `lake build`."

def challengeAbsent : String :=
  "lakefile.lean declares lean_lib «Challenge», but Challenge.lean does not exist, so nothing states the challenge. \
    Create Challenge.lean with the headlines, their holes, and a kill for each, delete owned.lock if there is one, \
    then run `lake build`."

def challengeOf (pkg : Package) : IO (Except String Lake.Module) := do
  let some challenge := pkg.findModule? `Challenge | return .error challengeUndeclared
  unless ← challenge.leanFile.pathExists do return .error challengeAbsent
  return .ok challenge

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

def lexical (path : System.FilePath) : System.FilePath :=
  System.mkFilePath <| path.components.foldl (init := []) fun parts part =>
    if part == "." then parts else if part == ".." && parts.length > 1 then parts.dropLast else parts ++ [part]

def hiddenFromSandbox (workspace : Workspace) (root : Package) :
    IO (Array (Name × System.FilePath × System.FilePath)) := do
  let rootDir ← IO.FS.realPath root.dir
  let mut hidden := #[]
  for pkg in workspace.packages do
    let real ← IO.FS.realPath pkg.dir
    if within real rootDir then continue
    let configured := lexical (rootDir / pkg.relDir)
    if let some dir := [configured, real].find? fun dir => sandboxCovers.any (within dir ·) then
      hidden := hidden.push (pkg.baseName, dir, real)
  return hidden

def lineOf (file : System.FilePath) (holds : String → Bool) : IO (Option (Nat × String)) := do
  unless ← file.pathExists do return none
  return ((← IO.FS.readFile file).splitOn "\n").zipIdx.findSome? fun (line, index) =>
    if holds line then some (index + 1, line.trimAscii.toString) else none

def statementTarget : String :=
  "@[default_target]\ntarget statement pkg : Unit := do\n  \
    return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())"

def builtinLintLine (pkg : Package) : IO (Option Nat) := do
  unless pkg.config.builtinLint? == some true do return none
  return some (((← lineOf (pkg.dir / "lakefile.lean") (·.contains "builtinLint")).map (·.1)).getD 1)

def setupProblems (pkg : Package) (next : String) : IO (Array String) := do
  let mut problems := #[]
  unless pkg.lintDriver == "software_challenge/lint_challenge" do
    problems := problems.push s!"lakefile.lean: the package block does not set \
      `lintDriver := \"software_challenge/lint_challenge\"`, so `lake lint` does not run the audit, and a `sorry` or \
      an unproved headline goes unreported. Add `lintDriver := \"software_challenge/lint_challenge\"` to the package \
      block of lakefile.lean, delete owned.lock and run `lake build`, then run `{next}`."
  unless pkg.defaultTargets.contains `statement do
    problems := problems.push s!"lakefile.lean: the package has no `statement` default target, so `lake build` \
      neither checks the statement nor writes comparator.json for the comparator. Add these lines to lakefile.lean:\n\
      {statementTarget}\nthen delete owned.lock and run `lake build`, then run `{next}`."
  if let some line ← builtinLintLine pkg then
    problems := problems.push s!"lakefile.lean:{line}: the package block sets `builtinLint := true`, but `lake lint` \
      already runs Lean's linters through software_challenge/lint_challenge, so they would run twice. Remove that \
      line, delete owned.lock and run `lake build`, then run `{next}`."
  return problems

def importsChallenge (catalog : Array Lake.Module) (challenge : Lake.Module) : FetchM (Option String) := do
  for mod in catalog do
    unless (← (← mod.imports.fetch).await).any (·.name == challenge.name) do continue
    let (line, text) := (← lineOf mod.leanFile fun line =>
      let words := (line.splitOn " ").filter (!·.isEmpty)
      words.contains "import" && words.contains challenge.name.toString).getD (1, s!"import {challenge.name}")
    let spec := (catalog.find? fun other => other.name.components.any (·.toString == "CoreSpec")).map (·.name)
    return some s!"{mod.relLeanFile}:{line}: {mod.name} imports {challenge.name}, whose holes share names with the \
      solution's definitions, so the solution cannot be checked against it. Replace `{text}` at \
      {mod.relLeanFile}:{line} with imports of the CoreSpec and WorldSpec modules {mod.name} uses\
      {(spec.map fun spec => s!", such as `public import {spec}`").getD ""}, then run `lake build`."
  return none

def auditOutput (pkg : Package) (mode : String) (flags : Array String) (challenge : Lake.Module)
    (olean : System.FilePath) (catalog : Array Lake.Module) : JobM IO.Process.Output := do
  IO.Process.output {
    cmd := (← getLean).toString
    args := #["--run", (__dir__ / "Audit.lean").toString, mode] ++ flags ++
      pkg.leanExes.map (s!"--executable={·.config.root}") ++
      #[challenge.relLeanFile.toString, olean.toString] ++
      catalog.map fun mod => s!"{mod.name}={mod.relLeanFile}"
    cwd := some pkg.dir
    env := ← getAugmentedEnv
  }

def addFileTraces (pkg : Package) (files : List String) : JobM Unit := do
  addTrace (← BuildTrace.compute (TextFilePath.mk (__dir__ / "Audit.lean")))
  for file in files do
    if ← (pkg.dir / file).pathExists then addTrace (← BuildTrace.compute (TextFilePath.mk (pkg.dir / file)))

def specModule (mod : Lake.Module) : Bool :=
  mod.name.components.any fun part => part.toString == "CoreSpec" || part.toString == "WorldSpec"

package_facet softwareChallengeStatement pkg : Unit := do
  let some audit ← findModule? `SoftwareChallenge.Audit | error auditMissing
  let problems ← setupProblems pkg "lake build"
  unless problems.isEmpty do error ("\n".intercalate problems.toList)
  let challenge ← match ← challengeOf pkg with | .ok challenge => pure challenge | .error message => error message
  let catalog ← packageModules pkg challenge
  if let some message ← importsChallenge catalog challenge then error message
  let mut job := Job.nil.mix (← audit.leanArts.fetch)
  for mod in ← (← challenge.transImports.fetch).await do
    if mod.pkg.keyName == pkg.keyName then job := job.mix (← mod.leanArts.fetch)
  for mod in catalog do
    if specModule mod then job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do
    addFileTraces pkg ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "owned.lock"]
    addPureTrace (" ".intercalate (catalog.map fun mod => s!"{mod.name}={mod.relLeanFile}").toList) "modules"
    for mod in catalog.push challenge do
      if mod.name == challenge.name || specModule mod then
        addTrace (← BuildTrace.compute (TextFilePath.mk mod.leanFile))
    let report := pkg.buildDir / "softwareChallengeStatement.txt"
    let written := pkg.buildDir / "comparator.json"
    let current ← if ← (pkg.dir / "comparator.json").pathExists then
      some <$> IO.FS.readFile (pkg.dir / "comparator.json") else pure none
    let previous ← if ← written.pathExists then some <$> IO.FS.readFile written else pure none
    unless current.isSome && current == previous && (← (pkg.dir / "owned.lock").pathExists) do
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
  let challenge ← match ← challengeOf pkg with | .ok challenge => pure challenge | .error message => error message
  let catalog ← packageModules pkg challenge
  if let some message ← importsChallenge catalog challenge then error message
  let hidden ← hiddenFromSandbox (← getWorkspace) pkg
  let flags := (if pkg.defaultTargets.contains `statement then #["--target"] else #[]) ++
    hidden.map fun (name, dir, _) => s!"--hidden={name}={dir}"
  let mut job := (Job.nil.mix (← audit.leanArts.fetch)).mix (← challenge.leanArts.fetch)
  for mod in catalog do
    job := job.mix (← mod.leanArts.fetch)
  job.mapM fun _ => do
    IO.FS.writeFile (pkg.buildDir / "softwareChallenge.built") ""
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

def pendingCount (report : String) : Nat :=
  ((report.splitOn "\n").findSome? fun line => (line.dropPrefix? "Pending: ").bind (·.toString.toNat?)).getD 0

def auditSolution (pkg : Package) : ScriptM UInt32 := do
  let built := pkg.buildDir / "softwareChallenge.built"
  if ← built.pathExists then IO.FS.removeFile built
  try
    discard <| runBuild (pkg.fetchFacetJob `softwareChallenge)
  catch _ =>
    unless ← built.pathExists do
      IO.eprintln "lake lint could not build the package's modules, as printed above, so the audit did not run. Fix \
        each error above; when the linker reports a `multiple definition`, two modules define the same name, or two \
        executables define `main`, so rename one of them. Then run `lake lint`."
    return 1
  return if pendingCount (← IO.FS.readFile (pkg.buildDir / "softwareChallenge.txt")) == 0 then 0 else 2

def lintTargets (pkg : Package) : ScriptM (Array Lean.Name) := do
  let .ok challenge ← challengeOf pkg | return #[]
  runBuild do
    let catalog ← packageModules pkg challenge
    let mut imported : NameSet := {}
    for mod in catalog do
      for dependency in ← (← mod.transImports.fetch).await do
        imported := imported.insert dependency.name
    let roots := pkg.leanExes.map (·.config.root)
    let tops := (catalog.filter (!imported.contains ·.name)).map (·.name)
    return Job.pure (tops.filter (!roots.contains ·) ++ tops.filter roots.contains)

def lintChallenge (pkg : Package) : ScriptM UInt32 := do
  let args := #["lint", "--builtin-only"] ++ (← lintTargets pkg).map (·.toString)
  let linters ← (← IO.Process.spawn { cmd := (← getLake).toString, args, cwd := pkg.dir }).wait
  let code ← auditSolution pkg
  unless linters == 0 do
    IO.eprintln "Lean's linters report the problems `lake lint --builtin-only` printed above, so the solution is not \
      clean. Fix each at the file and line it names, then run `lake lint`."
    return 1
  if code == 2 then
    let count := pendingCount (← IO.FS.readFile (pkg.buildDir / "softwareChallenge.txt"))
    IO.eprintln s!"lake lint found no errors, but {count} {if count == 1 then "item is" else "items are"} pending, \
      as listed under Pending above, so the solution is not complete. Do each as it says, then run `lake lint`."
  return code

def reportSetup (pkg : Package) (next : String) : IO Bool := do
  let problems ← setupProblems pkg next
  for problem in problems do IO.eprintln problem
  return problems.isEmpty

script lint_challenge do
  let pkg ← getRootPackage
  unless ← reportSetup pkg "lake lint" do return 1
  lintChallenge pkg

def runChecks (lake : String) (pkg : Package) : ScriptM UInt32 := do
  let challenge ← match ← challengeOf pkg with
    | .ok challenge => pure challenge
    | .error message => do IO.eprintln message; return 1
  let modules ← runBuild do return Job.pure (← packageModules pkg challenge)
  let runner := pkg.buildDir / "softwareChallenge" / "Checks.lean"
  IO.FS.createDirAll (pkg.buildDir / "softwareChallenge")
  IO.FS.writeFile runner <| "\n".intercalate <| ["import SoftwareChallenge"] ++
    (modules.map (s!"import {·.name}")).toList ++
    [s!"run_cmd SoftwareChallenge.runChecks #[{", ".intercalate (modules.map fun mod =>
      s!"(`{mod.name}, {(toJson mod.relLeanFile.toString).compress})").toList}]", ""]
  let out ← IO.Process.output { cmd := lake, args := #["lean", runner.toString], cwd := pkg.dir }
  IO.print out.stdout
  IO.eprint out.stderr
  let missing := ((out.stdout ++ out.stderr).splitOn "Could not find native implementation of external declaration '")
  if let some rest := missing[1]? then
    let name := (rest.splitOn "'").headD rest
    let line ← lineOf (pkg.dir / "lakefile.lean") (·.contains "lean_lib")
    IO.eprintln s!"lakefile.lean:{(line.map (·.1)).getD 1}: the Checks could not run: they call {name}, an \
      `@[extern]` declaration, whose native code Lean's interpreter finds only in precompiled modules, and the \
      package does not precompile them. Add `precompileModules := true` to the package's default lean_lib in \
      lakefile.lean, delete owned.lock and run `lake build`, then run `lake test`."
    return 1
  return out.exitCode

script run_checks do
  runChecks (← getLake).toString (← getRootPackage)

def scriptLine (pkg : Package) (name : String) : IO String := do
  let line ← lineOf (pkg.dir / "lakefile.lean") fun line =>
    ((line.dropPrefix? "script ").map fun rest => (rest.toString.splitOn " ").head? == some name).getD false
  return s!"lakefile.lean:{(line.map (·.1)).getD 1}"

def ownTests (pkg : Package) (names : List String) : ScriptM UInt32 := do
  let mut worst := 0
  for name in names do
    match pkg.scripts.find? name.toName with
    | some found =>
      let code ← found.run []
      unless code == 0 do
        IO.eprintln s!"{← scriptLine pkg name}: script {name}, which testDriverArgs names, exited {code}, so the \
          package's own tests fail. Run `lake script run {name}` to see what it checks, fix it, then run `lake test`."
      worst := max worst code
    | none =>
      let line ← lineOf (pkg.dir / "lakefile.lean") (·.contains "testDriverArgs")
      IO.eprintln s!"lakefile.lean:{(line.map (·.1)).getD 1}: testDriverArgs names {name}, but lakefile.lean \
        declares no script {name}, so it cannot run. Declare `script {name} do …` in lakefile.lean, or remove \
        \"{name}\" from testDriverArgs, delete owned.lock, run `lake build`, then run `lake test`."
      worst := max worst 1
  return worst

script test_challenge (args) do
  let pkg ← getRootPackage
  unless ← reportSetup pkg "lake test" do return 1
  let checks ← runChecks (← getLake).toString pkg
  return max checks (← ownTests pkg args)

def tenths (ms : Nat) : String := s!"{ms / 1000}.{ms % 1000 / 100} s"

def comparatorRejections : Array (String × String × String) := #[
  ("kernel rejected the solution", "Lean's kernel rejected its proof or a declaration it uses, though the build \
    accepted it, as `debug.skipKernelTC` or `Lean.addDecl` allows", "Prove it without those"),
  ("theorem statement do not match", "the solution states it otherwise than Challenge.lean",
    "State it exactly as Challenge.lean does"),
  ("constant kind don't match", "the solution declares it as another kind of constant than Challenge.lean",
    "Declare it as Challenge.lean does"),
  ("Const not found in solution", "the solution does not declare it",
    "Prove it in Solution or a module Solution imports"),
  ("Const does not match between challenge and target", "the solution defines it otherwise than Challenge.lean",
    "Define it as Challenge.lean does"),
  ("Solution constant is not a definition", "the solution declares it as something other than a definition",
    "Declare it as a `def`"),
  ("Solution constant is not a theorem", "the solution declares it as something other than a theorem",
    "Declare it as a `theorem`"),
  ("Illegal axiom detected", "its proof uses an axiom beyond propext, Classical.choice, and Quot.sound",
    "Prove it without that axiom"),
  ("is not permitted; it is used by", "its proof uses an axiom beyond propext, Classical.choice, and Quot.sound",
    "Prove it without that axiom")]

def missingConstant? (text : String) : Option String :=
  (text.splitOn "\n").findSome? fun line =>
    if line.startsWith "PANIC at LeanExport" then
      match line.splitOn " not found in environment" with
      | [before, _] => (before.splitOn " ").getLast?
      | _ => none
    else none

def rejectionOf (output : IO.Process.Output) : Option (String × String) :=
  let text := output.stdout ++ output.stderr
  let lines := text.splitOn "\n"
  let signalled := lines.any fun line => match line.splitOn "exited with " with
    | [_, code] => (code.trimAscii.toString.toNat?.map fun code => decide (code ≥ 128)).getD false
    | _ => false
  if output.exitCode != 1 || lines.any (·.startsWith "bwrap:") then none
  else if let some name := missingConstant? text then
    some (s!"the solution does not declare {name}, which Challenge.lean states",
      s!"Prove {name} in Solution or a module Solution imports, as `lake lint` lists under Pending")
  else if signalled then none
  else (comparatorRejections.find? fun (verdict, _) => text.contains verdict).map fun (_, why, fix) => (why, fix)

def comparatorFailure (output : IO.Process.Output) : String :=
  let lines := ((output.stdout ++ output.stderr).splitOn "\n").filter fun line =>
    line.startsWith "error:" || line.startsWith "bwrap:" || line.startsWith "PANIC"
  (lines.getLast?.map (·.trimAscii.toString)).getD s!"exit {output.exitCode}"

def replayEach (lake : String) (dir buildDir : System.FilePath) : IO UInt32 := do
  let text ← IO.FS.readFile (dir / "comparator.json")
  let parsed : Except String (Json × Array String) := do
    let config ← Json.parse text
    return (config, ← config.getObjValAs? (Array String) "theorem_names")
  let (config, theorems) ← match parsed with
    | .ok parsed => pure parsed
    | .error problem => do
      IO.eprintln s!"comparator.json cannot be read: {problem}. `lake build` writes it from Challenge.lean: delete \
        comparator.json and run `lake build`, then run `lake script run software_challenge/replay`."
      return 2
  let challenge ← if ← (dir / "Challenge.lean").pathExists then IO.FS.readFile (dir / "Challenge.lean") else pure ""
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
  let lineOfTheorem := fun (name : String) =>
    let short := (name.splitOn ".").getLast?.getD name
    ((challenge.splitOn "\n").zipIdx.findSome? fun (line, index) =>
      if ((line.splitOn " ").filter (!·.isEmpty)).contains short && line.contains "theorem " then some (index + 1)
      else none).map (s!"Challenge.lean:{·}")
  let replayAgain := "then run `lake script run software_challenge/replay`"
  for (name, output, _) in done do
    unless output.exitCode == 0 do
      let place := ((lineOfTheorem name).map (s!" ({·})")).getD ""
      match rejectionOf output with
      | some (why, fix) =>
        IO.eprintln s!"`lake comparator` rejects {name}{place}: {why}. {fix}, {replayAgain}.\n\
          {output.stdout}{output.stderr}"
      | none =>
        IO.eprintln s!"`lake comparator` could not check {name}{place}: it exited {output.exitCode} without a \
          verdict ({comparatorFailure output}). Fix that cause, such as a dependency under /home, /root, /run, /tmp, \
          or /var, which its sandbox hides, {replayAgain}.\n{output.stdout}{output.stderr}"
  let lines := done.map fun (name, output, elapsed) =>
    if output.exitCode == 0 then s!"{name}  {tenths elapsed}"
    else if (rejectionOf output).isSome then s!"{name}  {tenths elapsed}  (rejected)"
    else s!"{name}  {tenths elapsed}  (could not run, exit {output.exitCode})"
  let accepted := (done.filter (·.2.1.exitCode == 0)).size
  let report := "\n".intercalate (lines.push s!"Replayed: {accepted} of {theorems.size} theorems in {tenths total}").toList
  IO.FS.writeFile (buildDir / "comparator.txt") (report ++ "\n")
  (← IO.getStderr).flush
  IO.println report
  if done.any fun (_, output, _) => (rejectionOf output).isSome then return 1
  if done.any (·.2.1.exitCode != 0) then return 2
  return 0

script replay do
  let pkg ← getRootPackage
  unless ← (pkg.dir / "comparator.json").pathExists do
    IO.eprintln "comparator.json is missing: `lake build` writes it from Challenge.lean, and replay reads it. Run \
      `lake build`, then run `lake script run software_challenge/replay`."
    return 1
  replayEach (← getLake).toString pkg.dir pkg.buildDir

script grade_packages do
  let workspace ← getWorkspace
  let entries ← (workspace.packages.filter (!·.isRoot)).mapM fun pkg => do
    return Json.mkObj [("type", "path"), ("scope", toJson pkg.scope), ("name", toJson pkg.baseName),
      ("manifestFile", toJson pkg.relManifestFile.toString), ("inherited", toJson false),
      ("dir", toJson (← IO.FS.realPath pkg.dir).toString), ("copy", toJson false),
      ("configFile", toJson pkg.relConfigFile.toString)]
  IO.println (Json.mkObj [("version", "1.3.0"), ("packages", toJson entries)]).pretty
  return 0

script grade_candidate (args) do
  let lake := (← getLake).toString
  let pkg ← getRootPackage
  let commit := args.headD "the candidate"
  let again := s!"then run `lake exe grade {commit}` from the base checkout"
  let hidden ← hiddenFromSandbox (← getWorkspace) pkg
  for (name, dir, real) in hidden do
    let move := if sandboxCovers.any (within real ·) then "" else s!", such as its real path {real}"
    IO.eprintln s!"cannot judge: the comparator's sandbox hides package {name} at {dir}, because it mounts empty \
      directories over /home, /root, /run, /tmp, and /var, so `lake comparator` cannot build {commit}. In \
      lakefile.lean, require {name} from git or from a directory outside those{move}, delete owned.lock, run \
      `lake build`, and commit, {again}."
  unless hidden.isEmpty do return 3
  let problems ← setupProblems pkg s!"lake exe grade {commit}"
  for problem in problems do
    IO.eprintln s!"cannot judge: {problem} Make that change in the base, commit it, and merge it into {commit}."
  unless problems.isEmpty do return 3
  let refuse (step : String) : ScriptM UInt32 := do
    IO.eprintln s!"refused: `{step}` fails on {commit}, as printed above. Fix what it reports in {commit}, {again}."
    return 10
  unless (← (← IO.Process.spawn { cmd := lake, args := #["build"], cwd := pkg.dir }).wait) == 0 do
    return ← refuse "lake build"
  match ← lintChallenge pkg with
  | 0 => pure ()
  | 2 =>
    IO.eprintln s!"refused: {commit} is not complete: `lake lint` lists pending items above. Finish them in \
      {commit}, {again}."
    return 10
  | _ => return ← refuse "lake lint"
  unless (← runChecks lake pkg) == 0 do return ← refuse "lake script run software_challenge/run_checks"
  let own ← if pkg.testDriver == "software_challenge/test_challenge" then ownTests pkg pkg.testDriverArgs.toList
    else if pkg.testDriver.isEmpty then pure 0
    else (← IO.Process.spawn { cmd := lake, args := #["test"], cwd := pkg.dir }).wait
  unless own == 0 do
    IO.eprintln s!"refused: the package's own tests fail on {commit}, as printed above. Fix them in {commit}, \
      {again}."
    return 10
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
  relocks : Bool := false
  exits : Exits := {}

def replacing (old new : String) (text : String) : Option String :=
  if (text.splitOn old).length == 2 then some (text.replace old new) else none

def appending (addition : String) (text : String) : Option String := some (text ++ addition)

def matrixLayers : List String := ["build", "lint", "test", "comparator", "grade"]

def challengeFile : System.FilePath := "Challenge.lean"
def coreCodeFile : System.FilePath := "ConstantFolding" / "CoreCode.lean"
def worldCodeFile : System.FilePath := "ConstantFolding" / "WorldCode.lean"
def solutionFile : System.FilePath := "ConstantFolding" / "Solution.lean"

def weakened : Edits := [
  (challengeFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :="
    "theorem fold_idempotent (e : Expr) (_ : normal e = true) : fold (fold e) = fold e :="),
  (challengeFile, replacing "    ¬ ∀ e : Expr, (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"
    "    ¬ ∀ e : Expr, normal e = true → (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"),
  (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :="
    "theorem fold_idempotent (e : Expr) (_ : normal e = true) : fold (fold e) = fold e :="),
  (solutionFile, replacing "    ¬ ∀ e : Expr, (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"
    "    ¬ ∀ e : Expr, normal e = true → (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"),
  (solutionFile, replacing "  have := h (.lit 0)\n" "  have := h (.lit 0) rfl\n")]

def dropsKillProof : System.FilePath × (String → Option String) :=
  (solutionFile, replacing "theorem fold_normalizes_rejects_identity : ¬ ∀ e, normal (id e) = true := by\n  \
    intro h\n  exact absurd (h (.add (.lit 1) (.lit 2))) (by decide)\n\n" "")

def restated : Edits := [
  (challengeFile, replacing "(h : fold (.lit n) = .lit m) : m = n := by" "(h : fold (.lit n) = .lit m) : n = m := by"),
  (challengeFile, replacing "= .lit m → m = n := by" "= .lit m → n = m := by")]

def mutants : List Mutant := [
  { name := "owner-unchanged" },
  { name := "owner-drops-kill", exits := { build := 1, lint := 1, comparator := 1, grade := 3 }, owner := [
      (challengeFile, replacing "@[kills fold_normalizes] theorem fold_normalizes_rejects_identity : \
        ¬ ∀ e, normal (id e) = true := by\n  sorry\n\n" "")] },
  { name := "owner-restates-headline", exits := { lint := 2, comparator := 1, grade := 1 }, owner := restated },
  { name := "owner-breaks-solution", exits := { build := 1, lint := 1, test := 1, comparator := 1, grade := 1 }, owner := [
      ("ConstantFolding" / "CoreSpec.lean", replacing "@[expose] def Expr.isLit : Expr → Bool"
        "@[expose] def Expr.isLiteral : Expr → Bool"),
      ("ConstantFolding" / "CoreSpec.lean", replacing "!(a.isLit && b.isLit)" "!(a.isLiteral && b.isLiteral)")] },
  { name := "owner-meta-imports-tooling", exits := { build := 1, lint := 1, grade := 3 }, owner := [
      ("ConstantFolding" / "Notation.lean", appending "module\n\npublic section\n\ndef ConstantFolding.notationLevel : Nat := 1\n"),
      ("ConstantFolding" / "CoreSpec.lean", replacing "module\n\npublic section\n"
        "module\n\nmeta import ConstantFolding.Notation\n\npublic section\n")] },
  { name := "owner-narrows-roots", owner := [
      ("lakefile.lean", replacing "roots := #[`ConstantFolding.Solution]" "roots := #[`ConstantFolding.CoreCode]")] },
  { name := "owner-drops-precompile", exits := { test := 1, grade := 1 }, owner := [
      ("lakefile.lean", replacing "  precompileModules := true\n" "")] },
  { name := "owner-io-in-corespec", exits := { build := 1, lint := 1, grade := 3 }, owner := [
      ("ConstantFolding" / "CoreSpec.lean", appending "\ndef ConstantFolding.announce : IO Unit := pure ()\n")] },
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
  { name := "agent-edits-challenge", exits := { build := 1, lint := 1, grade := 1 }, agent := [
      (challengeFile, appending "\ntheorem graded : True := trivial\n")] },
  { name := "agent-adds-owned-file", exits := { build := 1, lint := 1, grade := 1 }, agent := [
      ("ConstantFolding" / "CoreSpec" / "Extra.lean",
        appending "module\n\npublic section\n\ntheorem ConstantFolding.extra : True := trivial\n")] },
  { name := "agent-weakens-solution", exits := { lint := 2, comparator := 1, grade := 1 }, agent := [
      (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :="
        "theorem fold_idempotent (e : Expr) (_ : normal e = true) : fold (fold e) = fold e :=")] },
  { name := "agent-drops-kill-proof", exits := { lint := 2, comparator := 1, grade := 1 }, agent := [dropsKillProof] },
  { name := "agent-lint-warning-pending", exits := { lint := 1, comparator := 1, grade := 1 }, agent := [
      (coreCodeFile, appending "\ntheorem ConstantFolding.self_eq (n : Nat) (h : n = n) : n = n := rfl\n"),
      dropsKillProof] },
  { name := "agent-relocks-weakened-statement", relocks := true, exits := { grade := 1 }, agent := weakened },
  { name := "agent-proves-outside-solution", exits := { lint := 2, comparator := 1, grade := 1 }, agent := [
      (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
        fold_eq_self_of_normal (fold e) (normal_fold e)\n\n" ""),
      ("ConstantFolding" / "Proofs.lean", appending "module\n\npublic import ConstantFolding.Solution\n\n\
        public section\n\nnamespace ConstantFolding\n\ntheorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
        fold_eq_self_of_normal (fold e) (normal_fold e)\n\nend ConstantFolding\n")] }]

def scrubbedEnv : Array (String × Option String) :=
  #[("GIT_DIR", none), ("GIT_WORK_TREE", none), ("GIT_INDEX_FILE", none), ("SOFTWARE_CHALLENGE_JOBS", some "1")]

def runIn (dir : System.FilePath) (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := dir, env := scrubbedEnv }

def succeedIn (dir : System.FilePath) (cmd : String) (args : Array String) : IO Unit := do
  let out ← runIn dir cmd args
  unless out.exitCode == 0 do
    throw <| IO.userError s!"`{cmd} {" ".intercalate args.toList}` exited {out.exitCode} in {dir}, as printed below, \
      so the matrix cannot set up its scratch copy. Fix what it reports in the template or the library, then run \
      `lake test`.\n{out.stdout}{out.stderr}"

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

def stepLayers : List String := ["build", "lint", "test", "comparator"]

def layerOutput (lake : String) (dir : System.FilePath) : String → IO IO.Process.Output
  | "comparator" => do
    let built ← runIn dir lake #["build", "Challenge"]
    if built.exitCode == 0 then runRetrying dir lake #["comparator"] else pure built
  | layer => runIn dir lake #[layer]

def applyEdits (dir : System.FilePath) (m : Mutant) (edits : Edits) : IO Unit := do
  for (file, edit) in edits do
    IO.FS.createDirAll (dir / file).parent.get!
    let text ← if ← (dir / file).pathExists then IO.FS.readFile (dir / file) else pure ""
    let some edited := edit text | throw <| IO.userError s!"{m.name}: the text its edit of {file} replaces does not \
      occur exactly once in that file, so the matrix cannot apply the mutant. Update that `replacing` text for \
      {m.name} in lakefile.lean to match the file it edits, then run `lake test`."
    IO.FS.writeFile (dir / file) edited

def relock (lake : String) (dir : System.FilePath) : IO IO.Process.Output := do
  IO.FS.removeFile (dir / "owned.lock")
  runIn dir lake #["build", ":softwareChallengeStatement"]

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
    throw <| IO.userError s!"{m.name}: reverting it left {copy} unlike the base, as the build and status below show, \
      so later mutants would see its state. Make revert in lakefile.lean undo what the mutant's edits or its build \
      left behind, then run `lake test`.\n{rebuilt.stdout}{rebuilt.stderr}{idle.stdout}{idle.stderr}{status.stdout}"

def runMutant (lake : String) (copy : System.FilePath) (owned : Array String) (config : String) (m : Mutant) :
    IO (Array (String × UInt32 × Nat) × String) := do
  try
    let mut log := ""
    unless m.owner.isEmpty do
      applyEdits copy m m.owner
      IO.FS.removeFile (copy / "owned.lock")
      unless m.agent.isEmpty do
        let recorded ← runIn copy lake #["build"]
        log := log ++ s!"--- {m.name} owner build exit {recorded.exitCode}\n{recorded.stdout}{recorded.stderr}"
    applyEdits copy m m.agent
    if m.relocks then
      let relocked ← relock lake copy
      log := log ++ s!"--- {m.name} relock build exit {relocked.exitCode}\n{relocked.stdout}{relocked.stderr}"
    let mut cells := #[]
    let mut verdict := false
    for layer in stepLayers do
      let start ← IO.monoMsNow
      let out ← layerOutput lake copy layer
      cells := cells.push (layer, out.exitCode, (← IO.monoMsNow) - start)
      log := log ++ s!"--- {m.name} {layer} exit {out.exitCode}\n{out.stdout}{out.stderr}"
      if layer == "comparator" then verdict := (rejectionOf out).isSome
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
  catch failure =>
    revert lake copy config m
    return (#[], toString failure)

def endToEnd : List (String × UInt32) := [("agent-honest", 0), ("agent-edits-challenge", 1),
  ("agent-forges-proof", 1), ("agent-relocks-weakened-statement", 1)]

def failingLake : String :=
  "#!/bin/sh\nfor arg in \"$@\"; do\n  if [ \"$arg\" = software_challenge/grade_candidate ]; then\n    \
    echo 'error: simulated failure before judging' >&2\n    exit 1\n  fi\ndone\nexec \"$REAL_LAKE\" \"$@\"\n"

def gradeEndToEnd (lake : String) (lsc root base : System.FilePath) :
    IO (Array (String × UInt32 × UInt32 × String)) := do
  for (name, _) in endToEnd do
    let some m := mutants.find? (·.name == name) | throw <| IO.userError s!"endToEnd in lakefile.lean names {name}, \
      but `mutants` has no mutant of that name, so it cannot be graded. Rename it to a mutant in `mutants`, then run \
      `lake test`."
    gitIn base #["checkout", "-q", "-b", name]
    applyEdits base m m.agent
    if m.relocks then
      let relocked ← relock lake base
      unless relocked.exitCode == 0 do
        throw <| IO.userError s!"{name}: `lake build` cannot record owned.lock after its edits, as printed below, so \
          the matrix cannot commit it. Make the edits of {name} in lakefile.lean build, then run `lake test`.\n\
          {relocked.stdout}{relocked.stderr}"
    gitIn base #["add", "-A"]
    gitIn base #["commit", "-q", "-m", name]
    gitIn base #["checkout", "-q", "base"]
  succeedIn base lake #["build", "software_challenge/grade", ":softwareChallengeStatement"]
  let wrapper := root / "failing-lake"
  IO.FS.writeFile wrapper failingLake
  IO.setAccessRights wrapper { user := { read := true, write := true, execution := true } }
  let gradeExe := lsc / ".lake" / "build" / "bin" / "grade"
  let failing : IO IO.Process.Output := IO.Process.output {
    cmd := gradeExe.toString, args := #["agent-honest"], cwd := base
    env := scrubbedEnv ++ #[("LAKE", some wrapper.toString), ("REAL_LAKE", some lake)] }
  let cases : List (String × UInt32 × IO IO.Process.Output) :=
    endToEnd.map (fun (name, expected) => (name, expected, runRetrying base lake #["exe", "grade", name])) ++
    [("a commit whose grade steps fail to start", 3, failing),
      ("a missing commit", 3, runIn base lake #["exe", "grade", "absent"])]
  let tasks ← cases.mapM fun (name, expected, action) => do
    return (name, expected, ← IO.asTask action (prio := .dedicated))
  tasks.toArray.mapM fun (name, expected, task) => do
    let out ← IO.ofExcept task.get
    return (name, expected, out.exitCode, out.stdout ++ out.stderr)

partial def copyTree (source destination : System.FilePath) : IO Unit := do
  if ← source.isDir then
    for entry in ← source.readDir do
      unless entry.fileName == ".lake" || entry.fileName == "comparator.json" do
        copyTree entry.path (destination / entry.fileName)
  else
    IO.FS.createDirAll destination.parent.get!
    IO.FS.writeBinFile destination (← IO.FS.readBinFile source)

def inRepoFiles : List System.FilePath := ["lakefile.lean", "lake-manifest.json", "lean-toolchain", ".gitignore",
  "Audit.lean", "SoftwareChallenge.lean", "SoftwareChallenge", "Examples" / "ConstantFolding"]

def replacedJudge : Mutant := { name := "agent-replaces-the-judge", agent := [
  ("lakefile.lean", replacing "script grade_candidate (args) do\n"
    "script grade_candidate (_args) do\n  return 0\n\nscript grade_candidate_replaced (args) do\n"),
  ("Examples" / "ConstantFolding" / coreCodeFile, appending "\ntheorem ConstantFolding.broken : False := rfl\n")] }

def inRepoGrade (lake : String) (lsc root : System.FilePath) : IO (String × UInt32 × UInt32 × String) := do
  let repo := root / "inrepo"
  for file in inRepoFiles do copyTree (lsc / file) (repo / file)
  let template := repo / "Examples" / "ConstantFolding"
  gitIn repo #["init", "-q"]
  gitIn repo #["add", "-A"]
  gitIn repo #["commit", "-q", "-m", "base"]
  gitIn repo #["branch", "-M", "base"]
  gitIn repo #["checkout", "-q", "-b", replacedJudge.name]
  applyEdits repo replacedJudge replacedJudge.agent
  gitIn repo #["add", "-A"]
  gitIn repo #["commit", "-q", "-m", replacedJudge.name]
  gitIn repo #["checkout", "-q", "base"]
  let out ← runRetrying template lake #["exe", "grade", replacedJudge.name]
  return ("an in-repo candidate that replaces the library's grade_candidate", 1, out.exitCode,
    out.stdout ++ out.stderr)

def matrixBase (lake : String) (lsc root : System.FilePath) : IO System.FilePath := do
  let base := root / "base"
  copyTree (lsc / "Examples" / "ConstantFolding") base
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

def mismatch (name : String) (wrong : Array (String × UInt32 × UInt32)) : String :=
  s!"{name}: {", ".intercalate (wrong.map fun (layer, code, expected) =>
    s!"{layer} exited {code}, expected {expected}").toList}, so those steps judge this mutant otherwise than the matrix \
    states, as the log below shows. Restore the rule that decided it, or change the mutant's `exits` in `mutants` in \
    lakefile.lean if the guarantee changed, then run `lake test`."

script test_matrix do
  let lake := (← getLake).toString
  let lsc ← IO.FS.realPath (← getRootPackage).dir
  let root := lsc / ".lake" / "build" / "matrix"
  if ← root.pathExists then IO.FS.removeDirAll root
  IO.FS.createDirAll root
  try
    let inRepo ← IO.asTask (inRepoGrade lake lsc root) (prio := .dedicated)
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
    let graded ← IO.asTask (gradeEndToEnd lake lsc root base) (prio := .dedicated)
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
      if cells.isEmpty then
        failed := true
        IO.eprintln log
        rows := rows.push s!"| {m.name} | **could not run** |"
        continue
      let wrong := cells.filterMap fun (layer, code, _) =>
        if code == m.exits.of layer then none else some (layer, code, m.exits.of layer)
      unless wrong.isEmpty do
        failed := true
        IO.eprintln s!"{mismatch m.name wrong}\n{log}"
      rows := rows.push s!"| {m.name} | {" | ".intercalate (cells.map fun (layer, code, ms) =>
        let mark := if code == m.exits.of layer then "" else "**"
        s!"{mark}{cellOf layer code}{mark} {tenths ms}").toList} |"
    rows := rows.push "\nThe grade column follows from the base's statement check, the owned-file diff, and the four \
      steps; `lake exe grade` ran end to end on:"
    for (name, expected, code, log) in (← IO.ofExcept graded.get).push (← IO.ofExcept inRepo.get) do
      if code != expected then
        failed := true
        IO.eprintln s!"lake exe grade on {name} exited {code}, expected {expected}, as the log below shows, so grade \
          no longer decides that case as the matrix states. Restore what decided it in SoftwareChallenge/Grade.lean or \
          grade_candidate in lakefile.lean, or change its expectation in lakefile.lean if the guarantee changed, then \
          run `lake test`.\n{log}"
      rows := rows.push s!"- {name}: exit {code}{if code == expected then "" else s!", expected {expected}"}"
    IO.FS.writeFile (lsc / ".lake" / "build" / "grade.md") ("\n".intercalate rows.toList ++ "\n")
    IO.println ("\n".intercalate rows.toList)
    return if failed then 1 else 0
  finally
    IO.FS.removeDirAll root

def sandboxFiles (lsc scratch linked : System.FilePath) : List (System.FilePath × String) := [
  ("hidden" / "lakefile.lean", "import Lake\nopen Lake DSL\npackage «hidden»\n"),
  ("consumer" / ".gitignore", "/.lake\n/comparator.json\n"),
  ("consumer" / "lakefile.lean", s!"import Lake\nopen Lake DSL\n\npackage «consumer» where\n  \
    lintDriver := \"software_challenge/lint_challenge\"\n\n\
    require software_challenge from \"{lsc}\"\nrequire hidden from \"{scratch / "hidden"}\"\n\
    require linked from \"{linked}\"\n\n\
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
  let visible := lsc / ".lake" / "build" / "sandbox-linked"
  try
    let consumer := scratch / "consumer"
    IO.FS.createDirAll visible
    IO.FS.writeFile (visible / "lakefile.lean") "import Lake\nopen Lake DSL\npackage «linked»\n"
    discard <| IO.Process.output { cmd := "ln", args := #["-s", visible.toString, (scratch / "linked").toString] }
    for (file, text) in sandboxFiles lsc scratch (scratch / "linked") do
      IO.FS.createDirAll (scratch / file).parent.get!
      IO.FS.writeFile (scratch / file) text
    IO.FS.writeFile (consumer / "lean-toolchain") (← IO.FS.readFile (lsc / "lean-toolchain"))
    succeedIn consumer lake #["build"]
    let lint ← runIn consumer lake #["lint"]
    gitIn consumer #["init", "-q"]
    gitIn consumer #["add", "-A"]
    gitIn consumer #["commit", "-q", "-m", "consumer"]
    let grade ← runIn consumer lake #["exe", "grade", "HEAD"]
    let hides := fun (name : String) => s!"the comparator's sandbox hides package {name}"
    let lintText := lint.stdout ++ lint.stderr
    let gradeText := grade.stdout ++ grade.stderr
    unless lint.exitCode == 2 && lintText.contains (hides "hidden") && lintText.contains (hides "linked") &&
        grade.exitCode == 3 && gradeText.contains (hides "hidden") do
      IO.eprintln s!"a dependency the comparator's sandbox hides was not reported: lake lint exited {lint.exitCode}, \
        expected 2 naming hidden and linked, and lake exe grade exited {grade.exitCode}, expected 3 naming hidden, \
        as the log below shows. Restore the check in hiddenFromSandbox in lakefile.lean, then run `lake test`.\n\
        {lintText}\n{gradeText}"
      return 1
    let config := consumer / "lakefile.lean"
    let solutionFile := consumer / "Consumer" / "Solution.lean"
    IO.FS.writeFile (consumer / "Consumer" / "Proofs.lean") "module\n\npublic import Consumer.CoreCode\n\n\
      public section\n\ntheorem zero_eq (n : Nat) (h : n = n) : zero 0 = 0 := rfl\n"
    IO.FS.writeFile solutionFile ((← IO.FS.readFile solutionFile).replace "public import Consumer.CoreCode\n"
      "public import Consumer.CoreCode\npublic import Consumer.Proofs\n")
    IO.FS.writeFile config ((← IO.FS.readFile config).replace "roots := #[`Consumer.Solution]"
      "roots := #[`Consumer.CoreCode]")
    IO.FS.removeFile (consumer / "owned.lock")
    succeedIn consumer lake #["build"]
    let unreached ← runIn consumer lake #["lint"]
    let unreachedText := unreached.stdout ++ unreached.stderr
    unless unreached.exitCode == 1 &&
        unreachedText.contains "Consumer/Proofs.lean:7: Lean's linter linter.unusedVariables reports" do
      IO.eprintln s!"a linter warning in Consumer/Proofs.lean, a module the default roots do not reach, was not \
        reported: lake lint exited {unreached.exitCode}, expected 1 with an error naming Consumer/Proofs.lean:7, \
        as the log below shows. Restore `warned` in SoftwareChallenge/Audit.lean, then run `lake test`.\n\
        {unreachedText}"
      return 1
    let brokenFile := consumer / "Consumer" / "Broken.lean"
    IO.FS.writeFile brokenFile "module\n\npublic section\n\ndef broken : Nat := \"text\"\n"
    let broken ← runIn consumer lake #["lint"]
    let brokenText := broken.stdout ++ broken.stderr
    IO.FS.removeFile brokenFile
    unless broken.exitCode == 1 && brokenText.contains "lake lint could not build the package's modules" do
      IO.eprintln s!"lake lint on a package with a module that does not compile exited {broken.exitCode}, expected 1 \
        saying that it could not build the package's modules, as the log below shows. Restore that message in \
        auditSolution in lakefile.lean, then run `lake test`.\n{brokenText}"
      return 1
    let configured ← IO.FS.readFile config
    IO.FS.writeFile config (configured.replace "  lintDriver :=" "  builtinLint := true\n  lintDriver :=")
    let twice ← runIn consumer lake #["lint"]
    unless twice.exitCode == 1 && (twice.stdout ++ twice.stderr).contains "sets `builtinLint := true`" do
      IO.eprintln s!"lake lint on a package that sets `builtinLint := true` exited {twice.exitCode}, expected 1 \
        naming that setting, as the log below shows, so Lean's linters would run twice unreported. Restore the \
        builtinLint check in lint_challenge in lakefile.lean, then run `lake test`.\n{twice.stdout}{twice.stderr}"
      return 1
    IO.FS.writeFile config (configured.replace "  lintDriver := \"software_challenge/lint_challenge\"\n" "")
    let undriven ← runIn consumer lake #["build"]
    unless undriven.exitCode == 1 && (undriven.stdout ++ undriven.stderr).contains "does not set" do
      IO.eprintln s!"lake build on a package without lintDriver exited {undriven.exitCode}, expected 1 naming the \
        missing `lintDriver`, as the log below shows, so `lake lint` would skip the audit unreported. Restore the \
        lintDriver check in setupProblems in lakefile.lean, then run `lake test`.\n{undriven.stdout}{undriven.stderr}"
      return 1
    IO.FS.writeFile config (configured.replace statementTarget "")
    let untargeted ← runIn consumer lake #["lint"]
    unless untargeted.exitCode == 1 && (untargeted.stdout ++ untargeted.stderr).contains "no `statement` default target" do
      IO.eprintln s!"lake lint on a package without the statement target exited {untargeted.exitCode}, expected 1 \
        naming the missing target, as the log below shows, so `lake build` would check no statement unreported. \
        Restore the statement-target check in setupProblems in lakefile.lean, then run `lake test`.\n\
        {untargeted.stdout}{untargeted.stderr}"
      return 1
    return 0
  finally
    IO.FS.removeDirAll scratch
    if ← visible.pathExists then IO.FS.removeDirAll visible

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

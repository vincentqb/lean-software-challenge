import Lean.Data.Json
import Lean.Elab.ParseImportsFast
import SoftwareChallenge.Problem

namespace SoftwareChallenge.Grade

open Lean System

inductive Stage where
  | commit | statement | owned | dependencies | worktree | build | lint | test | comparator
  deriving BEq

def Stage.order : List Stage := [.commit, .statement, .owned, .dependencies, .worktree, .build, .lint, .test, .comparator]

def Stage.command : Stage → String
  | .commit => "git rev-parse"
  | .statement | .dependencies => "lake build :softwareChallengeStatement"
  | .owned => "git diff"
  | .worktree => "git worktree add"
  | .build => "lake build"
  | .lint => "lake lint"
  | .test => "lake test"
  | .comparator => "lake comparator"

inductive Verdict where
  | accept | refuse | cannotJudge
  deriving BEq

def Verdict.code : Verdict → UInt32
  | .accept => 0
  | .refuse => 1
  | .cannotJudge => 3

structure Observation where
  stage : Stage
  verdict : Verdict
  detail : String

def decide (observations : List Observation) : Verdict :=
  match observations.find? (·.verdict != .accept) with
  | some stopped => stopped.verdict
  | none => if observations.map (·.stage) == Stage.order then .accept else .cannotJudge

def rejections : List (String × String × String) := [
  ("kernel rejected the solution", "Lean's kernel rejects a proof that the build accepted",
    "Prove it without `debug.skipKernelTC` or `Lean.addDecl`"),
  ("Challenge and solution theorem statement do not match", "the solution states a theorem otherwise than the challenge",
    "State it exactly as the challenge does"),
  ("Challenge and solution constant kind don't match", "the solution declares a target as another kind of constant",
    "Declare it as the challenge does"),
  ("Const not found in solution", "the solution does not declare a target of the challenge",
    "Declare it in the solution module or a module it imports"),
  ("Const does not match between challenge and target", "the solution defines a constant otherwise than the challenge",
    "Define it exactly as the challenge does"),
  ("Solution constant is not a definition", "the solution declares a hole as something other than a definition",
    "Declare the hole as a `def`"),
  ("Solution constant is not a theorem", "the solution declares a theorem target as something other than a theorem",
    "Declare it as a `theorem`"),
  ("Illegal axiom detected", "a proof uses an axiom that comparator.json does not permit",
    "Prove it without that axiom"),
  ("is not permitted; it is used by", "a proof uses an axiom that comparator.json does not permit",
    "Prove it without that axiom")]

def rejection? (code : UInt32) (output : String) : Option (String × String) :=
  if code != 1 || output.contains "bwrap:" || output.contains "PANIC" then none
  else (rejections.find? (output.contains ·.1)).map (·.2)

def coveredRoots : List String := ["/home", "/root", "/run", "/tmp", "/var"]

def components (path : String) : List String := (path.splitOn "/").filter fun part => !part.isEmpty && part != "."

def within (path root : String) : Bool := (components root).isPrefixOf (components path)

def run (cmd : String) (args : Array String) (cwd : FilePath) : IO UInt32 := do
  (← IO.Process.spawn { cmd, args, cwd := some cwd }).wait

def output (cmd : String) (args : Array String) (cwd : FilePath) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := some cwd }

def firstLine (text : String) : String := ((text.splitOn "\n").headD "").trimAscii.toString

def quoted (word : String) : String := "'" ++ word.replace "'" "'\\''" ++ "'"

def sourceOf (module : Name) : String := "/".intercalate (module.components.map toString) ++ ".lean"

partial def importClosure (base : FilePath) (fileOf : Name → String) (file : String) (seen : Array String) :
    IO (Array String) := do
  if seen.contains file then return seen
  let header ← parseImports' (← IO.FS.readFile (base / file)) file
  header.imports.foldlM (init := seen.push file) fun seen dependency => do
    let path := fileOf dependency.module
    if ← (base / path).pathExists then importClosure base fileOf path seen else return seen

def ownedPaths (base : FilePath) (challenge : String) (sources : Array (Name × String)) : IO (Array String) := do
  let configs ← #["lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"].filterM
    fun (file : String) => (base / file).pathExists
  let fileOf := fun (module : Name) => ((sources.find? (·.1 == module)).map (·.2)).getD (sourceOf module)
  return configs ++ (← importClosure base fileOf challenge #[])

structure Context where
  lake : String
  base : FilePath
  candidate : String
  again : String
  baseRef : String
  merge : String
  stamp : String

def Context.scratch (context : Context) : FilePath := context.base / ".lake" / "grade"

def Context.worktree (context : Context) : FilePath := context.scratch / context.stamp

def Context.configFile (context : Context) : FilePath := context.scratch / s!"{context.stamp}.json"

abbrev Judge := ExceptT Observation IO

def stop {α : Type} (stage : Stage) (verdict : Verdict) (detail : String) : Judge α :=
  throw { stage, verdict, detail }

def guarded {α : Type} (context : Context) (stage : Stage) (action : Judge α) : Judge α :=
  ExceptT.mk do
    try action.run
    catch error => return .error { stage, verdict := .cannotJudge, detail := s!"cannot judge: grade's \
      `{stage.command}` stage failed with `{error}`, so grade cannot tell whether {context.candidate} is right. Run \
      `{stage.command}` in {context.base} to see the cause, fix it there, {context.again}." }

structure Dependency where
  name : String
  real : String
  overridden : Bool
  override : Json

def Dependency.parse (entry : Json) : Except String Dependency := do
  let name ← entry.getObjValAs? String "name"
  let real ← entry.getObjValAs? String "real"
  let field := fun (key fallback : String) => (entry.getObjValAs? String key).toOption.getD fallback
  return { name, real, overridden := (entry.getObjValAs? Bool "overridden").toOption.getD false
           override := Json.mkObj [("type", "path"), ("scope", field "scope" ""), ("name", name),
             ("manifestFile", field "manifestFile" "lake-manifest.json"), ("inherited", false), ("dir", real),
             ("copy", false), ("configFile", field "configFile" "lakefile.lean")] }

structure BaseFacts where
  config : String
  solution : String
  challenge : String
  sources : Array (Name × String)
  targets : Nat
  dependencies : Array Dependency

def stepFile (dir : FilePath) (name : String) : FilePath := dir / ".lake" / "build" / "softwareChallenge" / name

def commitStage (context : Context) : Judge Unit := do
  unless (← output "git" #["rev-parse", "--show-toplevel"] context.base).exitCode == 0 do
    stop .commit .cannotJudge s!"cannot judge: {context.base} is not in a git repository, so grade cannot compare \
      the candidate's owned files with it. Run `lake exe grade {context.candidate}` from a git checkout of the base."
  unless (← output "git" #["rev-parse", "--verify", "--quiet", s!"{context.candidate}^\{commit}"] context.base).exitCode
      == 0 do
    stop .commit .cannotJudge s!"cannot judge: {context.candidate} names no commit of the repository at \
      {context.base}, so grade cannot check it out. Pass a commit or branch of that repository, as in \
      `lake exe grade HEAD`."

def readJson (path : FilePath) : IO (Except String Json) := do
  unless ← path.pathExists do return .error s!"{path} is missing"
  return Json.parse (← IO.FS.readFile path)

def statementStage (context : Context) : Judge BaseFacts := do
  let base := context.base
  unless (← run context.lake #["build", ":softwareChallengeStatement"] base) == 0 do
    stop .statement .cannotJudge s!"cannot judge: the statement check fails in {base}, as printed above, so it \
      states no challenge to grade {context.candidate} against. Fix each error there as it says until `lake build` \
      passes in {base}, commit, {context.merge}, {context.again}."
  let file := base / "comparator.json"
  let plan := stepFile base "statement.json"
  match ← readJson file, ← readJson plan with
  | .ok config, .ok described =>
    let facts : Except String BaseFacts := do
      return { config := config.compress, solution := ← config.getObjValAs? String "solution_module"
               challenge := ← (← described.getObjVal? "challenge").getObjValAs? String "file"
               sources := ← (← described.getObjValAs? (Array Json) "modules").mapM fun source => do
                 return ((← source.getObjValAs? String "module").toName, ← source.getObjValAs? String "file")
               targets := (← config.getObjValAs? (Array Json) "theorem_names").size
               dependencies := ← (← described.getObjValAs? (Array Json) "packages").mapM Dependency.parse }
    match facts with
    | .ok facts => return facts
    | .error problem => stop .statement .cannotJudge s!"cannot judge: {file} or {plan} lacks what grade reads \
        ({problem}), so grade has no statement to compare {context.candidate} with. Run `lake build` in {base}, \
        {context.again}."
  | .error problem, _ | _, .error problem => stop .statement .cannotJudge s!"cannot judge: {problem}, so grade has \
      no statement to compare {context.candidate} with. Run `lake build` in {base}, {context.again}."

def ownedStage (context : Context) (facts : BaseFacts) : Judge String := do
  let base := context.base
  let candidate := context.candidate
  let gitFails := s!"cannot judge: `git diff {candidate}` fails in {base}, as printed above, so grade cannot compare \
    the owned files. Fix what git reports, {context.again}."
  let packagePrefix := firstLine (← output "git" #["rev-parse", "--show-prefix"] base).stdout
  let owned := (← ownedPaths base facts.challenge facts.sources).map fun path =>
    ":(top,literal)" ++ "/".intercalate (components packagePrefix ++ components path)
  let differ := fun (revisions : Array String) => run "git" (#["diff", "--quiet"] ++ revisions ++ #["--"] ++ owned) base
  match ← differ #[candidate] with
  | 0 => return packagePrefix
  | 1 => pure ()
  | _ => stop .owned .cannotJudge gitFails
  match ← differ #["HEAD"] with
  | 0 => pure ()
  | 1 =>
    discard <| run "git" (#["diff", "--stat", "HEAD", "--"] ++ owned) base
    stop .owned .cannotJudge s!"cannot judge: {base} has changes to the owned files listed above that are not \
      committed, so no commit holds the statement grade would check. Commit them in {base}, {context.merge}, \
      {context.again}."
  | _ => stop .owned .cannotJudge gitFails
  discard <| run "git" (#["diff", "--stat", candidate, "--"] ++ owned) base
  let mergeBase := firstLine (← output "git" #["merge-base", "HEAD", candidate] base).stdout
  if (← differ #[mergeBase, candidate]) == 0 then
    stop .owned .refuse s!"refused: {context.baseRef} changed the owned files listed above after {candidate} \
      branched from it, so {candidate} solves an older statement. To grade it against this one, {context.merge}, \
      {context.again}."
  let names ← output "git" (#["diff", "--name-only", "--no-renames", candidate, "--"] ++ owned) base
  let files := (names.stdout.splitOn "\n").filter (!·.isEmpty)
  let restore := " ".intercalate (files.map fun file => quoted s!":(top,literal){file}")
  let changed : Problem := {
    rule := .owned, place := s!"{files.headD facts.challenge}:1", next := s!"lake exe grade {candidate}"
    what := s!"{candidate} changes the owned files {", ".intercalate files}"
    why := s!"which Challenge.lean and its imports state, so {candidate} solves another challenge"
    fix := s!"Restore them on {candidate} (`git checkout {candidate} && git restore --source={context.baseRef} \
      --staged --worktree -- {restore} && git commit -m 'Restore the owned files' && git checkout {context.baseRef}`)" }
  stop .owned .refuse ("refused: " ++ changed.render)

def dependenciesStage (context : Context) (facts : BaseFacts) : Judge Unit := do
  let hidden := facts.dependencies.filter fun dependency => coveredRoots.any (within dependency.real ·)
  if hidden.isEmpty then return
  let base ← IO.FS.realPath context.base
  stop .dependencies .cannotJudge <| "\n".intercalate <| hidden.toList.map fun dependency =>
    let fix := if within dependency.real base.toString then
        s!"Clone the repository of {context.base} into a directory outside those, run `lake build` in the clone, \
          then run `lake exe grade {context.candidate}` there"
      else if dependency.overridden then
        s!"In {context.base / ".lake" / "package-overrides.json"}, set the `dir` of {dependency.name} to a directory \
          outside those, or delete its entry, run `lake build`, {context.again}"
      else s!"In lakefile.lean, require {dependency.name} from git or from a directory outside those, run \
        `lake build`, and commit, {context.again}"
    s!"cannot judge: the comparator's sandbox hides package {dependency.name} at {dependency.real}, because it \
      mounts empty directories over /home, /root, /run, /tmp, and /var, so `lake comparator` cannot build \
      {context.candidate}. {fix}."

def worktreeStage (context : Context) (packagePrefix : String) (facts : BaseFacts) : Judge FilePath := do
  IO.FS.createDirAll context.scratch
  unless (← run "git" #["worktree", "add", "--detach", context.worktree.toString, context.candidate]
      context.base) == 0 do
    stop .worktree .cannotJudge s!"cannot judge: `git worktree add` cannot check out {context.candidate} at \
      {context.worktree}, as printed above. Run `git worktree prune` in {context.base}, {context.again}."
  let checkout := context.worktree / packagePrefix
  IO.FS.createDirAll (checkout / ".lake")
  let overrides := Json.mkObj [("version", "1.3.0"), ("packages", toJson (facts.dependencies.map (·.override)))]
  IO.FS.writeFile (checkout / ".lake" / "package-overrides.json") overrides.pretty
  return checkout

def stepStage (context : Context) (checkout : FilePath) (stage : Stage) (step : String) : Judge Unit := do
  match ← run context.lake #[step] checkout with
  | 0 => return
  | 3 => stop stage .cannotJudge s!"cannot judge: `{stage.command}` stopped in {checkout} before judging, as printed \
      above, so grade cannot tell whether {context.candidate} is right. Run `{stage.command}` in a checkout of \
      {context.candidate} to see the cause, fix it there, {context.again}."
  | _ => stop stage .refuse s!"refused: `{stage.command}` fails on {context.candidate}, as printed above. Fix each \
      problem it reports in {context.candidate} as it says, {context.again}."

def comparator (context : Context) (checkout : FilePath) (config : String) : IO IO.Process.Output := do
  IO.FS.writeFile context.configFile config
  let attempt := output context.lake #["comparator", "--config", context.configFile.toString] checkout
  let mut out ← attempt
  for _ in [0:3] do
    unless out.exitCode != 0 && (out.stdout ++ out.stderr).contains "bwrap: Can't bind mount" do break
    IO.sleep 20000
    out ← attempt
  return out

def comparatorStage (context : Context) (checkout : FilePath) (facts : BaseFacts) : Judge Unit := do
  let out ← comparator context checkout facts.config
  IO.print out.stdout
  (← IO.getStdout).flush
  IO.eprint out.stderr
  if out.exitCode == 0 then return
  match rejection? out.exitCode (out.stdout ++ "\n" ++ out.stderr) with
  | some (reason, remedy) =>
    stop .comparator .refuse s!"refused: `lake comparator` rejects {context.candidate}, as printed above, because \
      {reason}. {remedy} in {facts.solution}, {context.again}."
  | none =>
    stop .comparator .cannotJudge s!"cannot judge: `lake comparator` exited {out.exitCode} without a verdict, as \
      printed above, so grade cannot tell whether {context.candidate} is right. Run `lake comparator` in a checkout \
      of {context.candidate} to see the cause, such as `bwrap` permissions or a build failure in its sandbox, fix \
      it there, {context.again}."

def judge (context : Context) (passed : IO.Ref (Array Observation)) : Judge Unit := do
  let accept := fun (stage : Stage) (detail : String) =>
    (passed.modify (·.push { stage, verdict := .accept, detail }) : IO Unit)
  guarded context .commit (commitStage context)
  accept .commit s!"{context.candidate} is a commit of the repository at {context.base}"
  let facts ← guarded context .statement (statementStage context)
  accept .statement s!"comparator.json states {facts.targets} theorems"
  let packagePrefix ← guarded context .owned (ownedStage context facts)
  accept .owned "the owned files are unchanged"
  guarded context .dependencies (dependenciesStage context facts)
  accept .dependencies s!"the comparator's sandbox sees all {facts.dependencies.size} dependencies"
  let checkout ← guarded context .worktree (worktreeStage context packagePrefix facts)
  accept .worktree s!"{context.candidate} is checked out at {checkout}"
  for (stage, step) in [(Stage.build, "build"), (.lint, "lint"), (.test, "test")] do
    guarded context stage (stepStage context checkout stage step)
    accept stage s!"`{stage.command}` passes on {context.candidate}"
  guarded context .comparator (comparatorStage context checkout facts)
  accept .comparator s!"`lake comparator` accepts {context.candidate}"

def clean (context : Context) : IO Unit := do
  discard <| output "git" #["worktree", "remove", "--force", context.worktree.toString] context.base
  if ← context.worktree.pathExists then IO.FS.removeDirAll context.worktree
  if ← context.configFile.pathExists then IO.FS.removeFile context.configFile

def grade (candidate : String) : IO UInt32 := do
  let base ← IO.currentDir
  let branch := firstLine (← output "git" #["rev-parse", "--abbrev-ref", "HEAD"] base).stdout
  let short := firstLine (← output "git" #["rev-parse", "--short", "HEAD"] base).stdout
  let baseRef := if branch == "HEAD" then short else branch
  let context : Context := {
    lake := (← IO.getEnv "LAKE").getD "lake", base, candidate, baseRef
    again := s!"then run `lake exe grade {candidate}`"
    merge := s!"merge {baseRef} into {candidate} (`git checkout {candidate} && git merge {baseRef} && git checkout \
      {baseRef}`)"
    stamp := s!"{← IO.monoNanosNow}-{← IO.Process.getPID}" }
  let passed ← IO.mkRef #[]
  let outcome ← try (judge context passed).run finally clean context
  let recorded ← passed.get
  let observations := match outcome with
    | .ok () => recorded
    | .error stopped => recorded.push stopped
  for observation in observations do
    unless observation.verdict == .accept do IO.eprintln observation.detail
  let verdict := decide observations.toList
  if verdict == .accept then
    IO.println s!"accepted: {candidate} proves every target that {base} states, and passes `lake build`, \
      `lake lint`, `lake test` and `lake comparator`."
  return verdict.code

end SoftwareChallenge.Grade

def main : List String → IO UInt32
  | [candidate] => do
    try SoftwareChallenge.Grade.grade candidate
    catch error =>
      IO.eprintln s!"cannot judge: grade stopped on `{error}` while it set up or removed its checkout of {candidate}, \
        so it cannot tell whether {candidate} is right. Make `git` and `lake` run in this directory, then run `lake \
        exe grade {candidate}`."
      return 3
  | _ => do
    IO.eprintln "usage: `lake exe grade <commit>` judges the candidate commit against this checkout's statement, \
      and exits 0 to accept, 1 to refuse, and 3 when it cannot judge."
    return 3

module

public import SoftwareChallenge.CoreCode.Grade
public import SoftwareChallenge.CoreCode.Format
public import SoftwareChallenge.Steps.Comparator
public import Lean.Data.Json

public section

namespace SoftwareChallenge.Steps.Grade

open Lean

def run (cmd : String) (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  (← IO.Process.spawn { cmd, args, cwd := some cwd }).wait

def output (cmd : String) (args : Array String) (cwd : System.FilePath) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := some cwd }

def firstLine (text : String) : String := ((text.splitOn "\n").headD "").trimAscii.toString

def quoted (word : String) : String := "'" ++ word.replace "'" "'\\''" ++ "'"

structure Context where
  lake : String
  base : System.FilePath
  candidate : String
  again : String
  baseRef : String
  merge : String
  stamp : String

def Context.scratch (context : Context) : System.FilePath := context.base / ".lake" / "grade"

def Context.worktree (context : Context) : System.FilePath := context.scratch / context.stamp

def Context.configFile (context : Context) : System.FilePath := context.scratch / s!"{context.stamp}.json"

abbrev Judge := ExceptT Observation IO

def stop {α : Type} (stage : Stage) (verdict : Verdict) (detail : String) : Judge α :=
  throw { stage, verdict, detail }

def stageWord : Stage → String
  | .lock => "lock"
  | .statement => "statement"
  | .owned => "owned"
  | .dependencies => "dependencies"
  | .worktree => "worktree"
  | .build => "build"
  | .lint => "lint"
  | .test => "test"
  | .comparator => "comparator"

def guarded {α : Type} (context : Context) (stage : Stage) (action : Judge α) : Judge α :=
  ExceptT.mk do
    try action.run
    catch error => return .error { stage, verdict := .cannotJudge, detail := s!"cannot judge: grade's \
      {stageWord stage} stage failed with `{error}`, so grade cannot tell whether {context.candidate} is right. Fix \
      what it reports, {context.again}." }

structure Dependency where
  name : Name
  real : String
  override : Json

def Dependency.parse (entry : Json) : Except String Dependency := do
  let name ← entry.getObjValAs? String "name"
  let real ← entry.getObjValAs? String "real"
  let field := fun (key fallback : String) => (entry.getObjValAs? String key).toOption.getD fallback
  return { name := name.toName, real, override := Json.mkObj [("type", "path"), ("scope", field "scope" ""),
    ("name", name), ("manifestFile", field "manifestFile" "lake-manifest.json"), ("inherited", false),
    ("dir", real), ("copy", false), ("configFile", field "configFile" "lakefile.lean")] }

def dependencies (text : String) : Except String (Array Dependency) := do
  (← (← Json.parse text).getObjValAs? (Array Json) "packages").mapM Dependency.parse

def overrides (dependencies : Array Dependency) : Json :=
  Json.mkObj [("version", "1.3.0"), ("packages", toJson (dependencies.map (·.override)))]

structure BaseFacts where
  lock : Array Lock.Entry
  config : Config
  dependencies : Array Dependency

def stepFile (dir : System.FilePath) (name : String) : System.FilePath :=
  dir / ".lake" / "build" / "softwareChallenge" / name

def lockStage (context : Context) : Judge Unit := do
  let base := context.base
  let candidate := context.candidate
  unless (← output "git" #["rev-parse", "--show-toplevel"] base).exitCode == 0 do
    stop .lock .cannotJudge s!"cannot judge: {base} is not in a git repository, so grade cannot compare the \
      candidate's owned files with it. Run `lake exe grade {candidate}` from a git checkout of the base."
  unless (← output "git" #["rev-parse", "--verify", "--quiet", s!"{candidate}^\{commit}"] base).exitCode == 0 do
    stop .lock .cannotJudge s!"cannot judge: {candidate} names no commit of the repository at {base}, so grade \
      cannot check it out. Pass a commit or branch of that repository, as in `lake exe grade HEAD`."

def statementStage (context : Context) : Judge BaseFacts := do
  let base := context.base
  let candidate := context.candidate
  unless (← run context.lake #["build", ":softwareChallengeStatement"] base) == 0 do
    stop .statement .cannotJudge s!"cannot judge: the statement check fails in {base}, as printed above, so it \
      states no challenge to grade {candidate} against. Fix each error there as it says until `lake build` passes \
      in {base}, commit, {context.merge}, {context.again}."
  let lock := base / "owned.lock"
  unless ← lock.pathExists do
    stop .statement .cannotJudge s!"cannot judge: {lock} is missing, so grade cannot tell which files {candidate} \
      must leave unchanged. Run `lake build` in {base} to record it, commit it, {context.merge}, {context.again}."
  let some entries := Lock.parse (← IO.FS.readFile lock) | stop .statement .cannotJudge s!"cannot judge: {lock} \
    is not an owned.lock that `lake build` writes, so grade cannot tell which files {candidate} must leave \
    unchanged. Delete it, run `lake build` in {base} to record it, and commit it, {context.merge}, {context.again}."
  let file := base / "comparator.json"
  unless ← file.pathExists do
    stop .statement .cannotJudge s!"cannot judge: the statement check wrote no comparator.json in {base}, so grade \
      has no statement to compare {candidate} with. Run `lake build` in {base}, {context.again}."
  let some config := Config.parse (← IO.FS.readFile file) | stop .statement .cannotJudge s!"cannot judge: {file} \
    is not a comparator configuration that `lake build` writes, so grade has no statement to compare {candidate} \
    with. Delete it, run `lake build` in {base}, {context.again}."
  let described := stepFile base "lake.json"
  let text ← if ← described.pathExists then IO.FS.readFile described else pure ""
  match dependencies text with
  | .ok found => return { lock := entries, config, dependencies := found }
  | .error problem => stop .statement .cannotJudge s!"cannot judge: {described} names no dependencies grade can \
      read ({problem}), so grade cannot give {candidate} the base's dependencies. Run `lake build` in {base}, \
      {context.again}."

def ownedStage (context : Context) (lock : Array Lock.Entry) : Judge String := do
  let base := context.base
  let candidate := context.candidate
  let gitFails := s!"cannot judge: `git diff {candidate}` fails in {base}, as printed above, so grade cannot compare \
    the owned files. Fix what git reports, {context.again}."
  let packagePrefix := firstLine (← output "git" #["rev-parse", "--show-prefix"] base).stdout
  let owned := Grade.ownedPathspecs packagePrefix lock
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
  stop .owned .refuse s!"refused: {candidate} changes the owned files {", ".intercalate files}, which state the \
    challenge, so {candidate} is not a solution of it. Restore them on {candidate} (`git checkout {candidate} && \
    git restore --source={context.baseRef} --staged --worktree -- {restore} && git commit -m 'Restore the owned \
    files' && git checkout {context.baseRef}`), {context.again}."

def dependenciesStage (context : Context) (facts : BaseFacts) : Judge Unit := do
  let hidden := facts.dependencies.filter (Sandbox.covers ·.real)
  if hidden.isEmpty then return
  let base ← IO.FS.realPath context.base
  stop .dependencies .cannotJudge <| "\n".intercalate <| hidden.toList.map fun dependency =>
    let fix := if Sandbox.within dependency.real base.toString then
        s!"Clone the repository of {context.base} into a directory outside those, run `lake build` in the clone, \
          then run `lake exe grade {context.candidate}` there"
      else s!"In lakefile.lean, require {dependency.name} from git or from a directory outside those, delete \
        owned.lock, run `lake build`, and commit, {context.again}"
    s!"cannot judge: the comparator's sandbox hides package {dependency.name} at {dependency.real}, because it \
      mounts empty directories over /home, /root, /run, /tmp, and /var, so `lake comparator` cannot build \
      {context.candidate}. {fix}."

def worktreeStage (context : Context) (packagePrefix : String) (facts : BaseFacts) : Judge System.FilePath := do
  IO.FS.createDirAll context.scratch
  unless (← run "git" #["worktree", "add", "--detach", context.worktree.toString, context.candidate]
      context.base) == 0 do
    stop .worktree .cannotJudge s!"cannot judge: `git worktree add` cannot check out {context.candidate} at \
      {context.worktree}, as printed above. Run `git worktree prune` in {context.base}, {context.again}."
  let checkout := context.worktree / packagePrefix
  IO.FS.createDirAll (checkout / ".lake")
  IO.FS.writeFile (checkout / ".lake" / "package-overrides.json") (overrides facts.dependencies).pretty
  return checkout

def stepStage (context : Context) (checkout : System.FilePath) (stage : Stage) (step status : String) :
    Judge Unit := do
  let candidate := context.candidate
  let code ← run context.lake #[step] checkout
  if code == 0 then return
  let file := stepFile checkout s!"{status}.status"
  let judged ← if ← file.pathExists then pure (← IO.FS.readFile file).trimAscii.toString.toNat? else pure none
  match judged with
  | some 2 => stop stage .refuse s!"refused: {candidate} is not complete: `lake {step}` lists pending items above. \
      Finish them in {candidate}, {context.again}."
  | some 3 | none => stop stage .cannotJudge s!"cannot judge: `lake {step}` exited {code} in {checkout} before \
      judging, as printed above, so grade cannot tell whether {candidate} is right. Fix the cause it reports, \
      {context.again}."
  | some _ => stop stage .refuse s!"refused: `lake {step}` fails on {candidate}, as printed above. Fix what it \
      reports in {candidate}, {context.again}."

def comparatorStage (context : Context) (checkout : System.FilePath) (config : Config) : Judge Unit := do
  let candidate := context.candidate
  let out ← Comparator.run context.lake checkout context.configFile config
  IO.print out.stdout
  (← IO.getStdout).flush
  IO.eprint out.stderr
  let text := out.stdout ++ "\n" ++ out.stderr
  if out.exitCode == 0 then return
  match Comparator.rejection? out.exitCode text with
  | some (.missing name) =>
    stop .comparator .refuse s!"refused: `lake comparator` rejects {candidate}: {Comparator.reason (.missing name)}, as \
      printed above. {Comparator.remedy config.solution (.missing name)}, {context.again}."
  | some rejection =>
    stop .comparator .refuse s!"refused: `lake comparator` rejects {candidate}: {Comparator.reason rejection}, as printed \
      above. {Comparator.remedy config.solution rejection} in {candidate}; `lake script run software_challenge/replay` in a \
      checkout of it names the theorem, {context.again}."
  | none =>
    stop .comparator .cannotJudge s!"cannot judge: `lake comparator` exited {out.exitCode} without a verdict, as \
      printed above, so grade cannot tell whether {candidate} is right. Fix the cause it reports, such as `bwrap` \
      permissions or a build failure in its sandbox, {context.again}."

def judge (context : Context) (passed : IO.Ref (Array Observation)) : Judge Unit := do
  let accept := fun (stage : Stage) (detail : String) =>
    (passed.modify (·.push { stage, verdict := .accept, detail }) : IO Unit)
  guarded context .lock (lockStage context)
  accept .lock s!"{context.candidate} is a commit of the repository at {context.base}"
  let facts ← guarded context .statement (statementStage context)
  accept .statement s!"owned.lock records {facts.lock.size} files, and comparator.json states \
    {facts.config.theorems.size} theorems and {facts.config.definitions.size} holes"
  let packagePrefix ← guarded context .owned (ownedStage context facts.lock)
  accept .owned "the owned files are unchanged"
  guarded context .dependencies (dependenciesStage context facts)
  accept .dependencies s!"the comparator's sandbox sees all {facts.dependencies.size} dependencies"
  let checkout ← guarded context .worktree (worktreeStage context packagePrefix facts)
  accept .worktree s!"{context.candidate} is checked out at {checkout}"
  for (stage, step, status) in [(Stage.build, "build", "statement"), (.lint, "lint", "lint"), (.test, "test", "test")] do
    guarded context stage (stepStage context checkout stage step status)
    accept stage s!"`lake {step}` passes on {context.candidate}"
  guarded context .comparator (comparatorStage context checkout facts.config)
  accept .comparator s!"`lake comparator` accepts {context.candidate}"

def clean (context : Context) : IO Unit := do
  discard <| output "git" #["worktree", "remove", "--force", context.worktree.toString] context.base
  if ← context.worktree.pathExists then IO.FS.removeDirAll context.worktree
  discard <| output "git" #["worktree", "prune"] context.base
  if ← context.configFile.pathExists then IO.FS.removeFile context.configFile

def grade (candidate : String) : IO UInt32 := do
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let base ← IO.currentDir
  let branch := firstLine (← output "git" #["rev-parse", "--abbrev-ref", "HEAD"] base).stdout
  let short := firstLine (← output "git" #["rev-parse", "--short", "HEAD"] base).stdout
  let baseRef := if branch == "HEAD" then short else branch
  let context : Context := {
    lake, base, candidate, baseRef
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
    unless observation.verdict == .accept || observation.detail.isEmpty do IO.eprintln observation.detail
  let verdict := Grade.decide observations.toList
  if verdict == .accept then
    IO.println s!"accepted: {candidate} proves every headline, kill, and witness that {base} states, and passes \
      `lake build`, `lake lint`, and `lake test`."
  return verdict.code

end SoftwareChallenge.Steps.Grade

def main : List String → IO UInt32
  | [candidate] => do
    try SoftwareChallenge.Steps.Grade.grade candidate
    catch error =>
      IO.eprintln s!"cannot judge: grade stopped on `{error}`, so it cannot tell whether {candidate} is right. Fix \
        what it reports, then run `lake exe grade {candidate}`."
      return 3
  | _ => do
    IO.eprintln "usage: lake exe grade <commit> judges the candidate commit against this checkout's statement, \
      and exits 0 to accept, 1 to refuse, and 3 when it cannot judge."
    return 3

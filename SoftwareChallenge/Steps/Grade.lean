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

def legacyEntries (text : String) : Option (Array Lock.Entry) :=
  ((text.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)).toArray.mapM fun line =>
    match line.splitOn " " with
    | digest :: first :: rest =>
      if digest.toNat?.isSome then some { digest, path := " ".intercalate (first :: rest) } else none
    | _ => none

def lockEntries (text : String) : Option (Array Lock.Entry) :=
  Lock.parse text <|> legacyEntries text

structure BaseFacts where
  overrides : Json
  packages : Array (Name × String)

def BaseFacts.parse (text : String) : Except String BaseFacts := do
  let overrides ← Json.parse text
  let packages ← (← overrides.getObjValAs? (Array Json) "packages").mapM fun entry => do
    return ((← entry.getObjValAs? String "name").toName, ← entry.getObjValAs? String "dir")
  return { overrides, packages }

def lockStage (context : Context) : Judge (Array Lock.Entry) := do
  let base := context.base
  let candidate := context.candidate
  unless (← output "git" #["rev-parse", "--show-toplevel"] base).exitCode == 0 do
    stop .lock .cannotJudge s!"cannot judge: {base} is not in a git repository, so grade cannot compare the \
      candidate's owned files with it. Run `lake exe grade {candidate}` from a git checkout of the base."
  unless (← output "git" #["rev-parse", "--verify", "--quiet", s!"{candidate}^\{commit}"] base).exitCode == 0 do
    stop .lock .cannotJudge s!"cannot judge: {candidate} names no commit of the repository at {base}, so grade \
      cannot check it out. Pass a commit or branch of that repository, as in `lake exe grade HEAD`."
  let lock := base / "owned.lock"
  unless ← lock.pathExists do
    stop .lock .cannotJudge s!"cannot judge: {lock} is missing, so grade cannot tell which files {candidate} must \
      leave unchanged. Run `lake build` in {base} to record it, commit it, {context.merge}, {context.again}."
  let some entries := lockEntries (← IO.FS.readFile lock) | stop .lock .cannotJudge s!"cannot judge: {lock} is \
    not an owned.lock that `lake build` writes, so grade cannot tell which files {candidate} must leave unchanged. \
    Delete it, run `lake build` in {base} to record it, and commit it, {context.merge}, {context.again}."
  return entries

def statementStage (context : Context) : Judge (Config × BaseFacts) := do
  let base := context.base
  let candidate := context.candidate
  unless (← run context.lake #["build", ":softwareChallengeStatement"] base) == 0 do
    stop .statement .cannotJudge s!"cannot judge: the statement check fails in {base}, as printed above, so it \
      states no challenge to grade {candidate} against. Fix each error there as it says until `lake build` passes \
      in {base}, commit, {context.merge}, {context.again}."
  let file := base / "comparator.json"
  unless ← file.pathExists do
    stop .statement .cannotJudge s!"cannot judge: the statement check wrote no comparator.json in {base}, so grade \
      has no statement to compare {candidate} with. Run `lake build` in {base}, {context.again}."
  let some config := Config.parse (← IO.FS.readFile file) | stop .statement .cannotJudge s!"cannot judge: {file} \
    is not a comparator configuration that `lake build` writes, so grade has no statement to compare {candidate} \
    with. Delete it, run `lake build` in {base}, {context.again}."
  let described ← output context.lake #["script", "run", "software_challenge/grade_packages"] base
  unless described.exitCode == 0 do
    IO.eprint described.stderr
    stop .statement .cannotJudge s!"cannot judge: `lake script run software_challenge/grade_packages` fails in \
      {base}, as printed above, so grade cannot give {candidate} the base's dependencies. Fix what it reports, \
      {context.again}."
  match BaseFacts.parse described.stdout with
  | .ok facts => return (config, facts)
  | .error problem => stop .statement .cannotJudge s!"cannot judge: `lake script run \
      software_challenge/grade_packages` in {base} printed no dependencies grade can read ({problem}), so grade \
      cannot give {candidate} the base's dependencies. Run it in {base}, fix what it reports, {context.again}."

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
  let hidden := facts.packages.filter fun (_, dir) => Sandbox.covers dir
  if hidden.isEmpty then return
  let base ← IO.FS.realPath context.base
  stop .dependencies .cannotJudge <| "\n".intercalate <| hidden.toList.map fun (name, dir) =>
    let fix := if Sandbox.within dir base.toString then
        s!"Clone the repository of {context.base} into a directory outside those, run `lake build` in the clone, \
          then run `lake exe grade {context.candidate}` there"
      else s!"In lakefile.lean, require {name} from git or from a directory outside those, delete owned.lock, run \
        `lake build`, and commit, {context.again}"
    s!"cannot judge: the comparator's sandbox hides package {name} at {dir}, because it mounts empty directories \
      over /home, /root, /run, /tmp, and /var, so `lake comparator` cannot build {context.candidate}. {fix}."

def worktreeStage (context : Context) (packagePrefix : String) (facts : BaseFacts) : Judge System.FilePath := do
  IO.FS.createDirAll context.scratch
  unless (← run "git" #["worktree", "add", "--detach", context.worktree.toString, context.candidate]
      context.base) == 0 do
    stop .worktree .cannotJudge s!"cannot judge: `git worktree add` cannot check out {context.candidate} at \
      {context.worktree}, as printed above. Run `git worktree prune` in {context.base}, {context.again}."
  let checkout := context.worktree / packagePrefix
  IO.FS.createDirAll (checkout / ".lake")
  IO.FS.writeFile (checkout / ".lake" / "package-overrides.json") facts.overrides.pretty
  return checkout

def stepStage (context : Context) (checkout : System.FilePath) (stage : Stage) (step : String) : Judge Unit := do
  let candidate := context.candidate
  match ← run context.lake #["script", "run", "software_challenge/grade_candidate", candidate, step] checkout with
  | 0 => pure ()
  | 10 => stop stage .refuse ""
  | 3 => stop stage .cannotJudge ""
  | code =>
    stop stage .cannotJudge s!"cannot judge: `lake script run software_challenge/grade_candidate {candidate} \
      {step}` exited {code} in {checkout} before judging, as printed above, so grade cannot tell whether \
      {candidate} is right. Fix the cause it reports, {context.again}."

def reason : Comparator.Rejection → String
  | .kernel => "Lean's kernel rejected a proof or a declaration it uses, though the build accepted it, as \
      `debug.skipKernelTC` or `Lean.addDecl` allows"
  | .statement => "the solution states a theorem otherwise than the challenge"
  | .kind => "the solution declares a constant of the challenge as another kind of constant"
  | .absent => "the solution does not declare a theorem or hole that the challenge states"
  | .unexported => "the solution's export lacks a constant that its proofs use"
  | .differs => "the solution defines a constant otherwise than the challenge"
  | .notDefinition => "the solution declares a hole as something other than a definition"
  | .notTheorem => "the solution declares a theorem of the challenge as something other than a theorem"
  | .axiomUsed => "a proof uses an axiom beyond propext, Classical.choice, and Quot.sound"
  | .missing name => s!"the solution does not declare {name}, which the challenge states"

def remedy (solution : Name) : Comparator.Rejection → String
  | .kernel => "Prove it without `debug.skipKernelTC` or `Lean.addDecl`"
  | .statement => "State it exactly as the challenge does"
  | .kind => "Declare it as the challenge does"
  | .absent => s!"Prove it in {solution} or a module it imports"
  | .unexported => s!"Declare that constant in {solution} or a module it imports"
  | .differs => "Define it as the challenge does"
  | .notDefinition => "Declare it as a `def`"
  | .notTheorem => "Declare it as a `theorem`"
  | .axiomUsed => "Prove it without that axiom"
  | .missing name => s!"Prove {name} in {solution} or a module it imports"

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
    stop .comparator .refuse s!"refused: `lake comparator` rejects {candidate}: {reason (.missing name)}, as \
      printed above. {remedy config.solution (.missing name)}, {context.again}."
  | some rejection =>
    stop .comparator .refuse s!"refused: `lake comparator` rejects {candidate}: {reason rejection}, as printed \
      above. {remedy config.solution rejection} in {candidate}; `lake script run software_challenge/replay` in a \
      checkout of it names the theorem, {context.again}."
  | none =>
    stop .comparator .cannotJudge s!"cannot judge: `lake comparator` exited {out.exitCode} without a verdict, as \
      printed above, so grade cannot tell whether {candidate} is right. Fix the cause it reports, such as `bwrap` \
      permissions or a build failure in its sandbox, {context.again}."

def judge (context : Context) (passed : IO.Ref (Array Observation)) : Judge Unit := do
  let accept := fun (stage : Stage) (detail : String) =>
    (passed.modify (·.push { stage, verdict := .accept, detail }) : IO Unit)
  let lock ← guarded context .lock (lockStage context)
  accept .lock s!"owned.lock records {lock.size} files"
  let (config, facts) ← guarded context .statement (statementStage context)
  accept .statement s!"comparator.json states {config.theorems.size} theorems and {config.definitions.size} holes"
  let packagePrefix ← guarded context .owned (ownedStage context lock)
  accept .owned "the owned files are unchanged"
  guarded context .dependencies (dependenciesStage context facts)
  accept .dependencies s!"the comparator's sandbox sees all {facts.packages.size} dependencies"
  let checkout ← guarded context .worktree (worktreeStage context packagePrefix facts)
  accept .worktree s!"{context.candidate} is checked out at {checkout}"
  for (stage, step) in [(Stage.build, "build"), (.lint, "lint"), (.test, "test")] do
    guarded context stage (stepStage context checkout stage step)
    accept stage s!"`lake {step}` passes on {context.candidate}"
  guarded context .comparator (comparatorStage context checkout config)
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

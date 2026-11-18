module

public section

namespace SoftwareChallenge.Grade

def run (cmd : String) (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  (← IO.Process.spawn { cmd, args, cwd := some cwd }).wait

def output (cmd : String) (args : Array String) (cwd : System.FilePath) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := some cwd }

def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

def firstLine (text : String) : String := ((text.splitOn "\n").headD "").trimAscii.toString

def lockedFiles (dir : System.FilePath) : IO (Option (Array String)) := do
  let lock := dir / "owned.lock"
  unless ← lock.pathExists do return none
  return some <| #["owned.lock"] ++ ((← IO.FS.readFile lock).splitOn "\n").toArray.filterMap fun line =>
    match line.splitOn " " with
    | [_, file] => some file
    | _ => none

def rejections : Array (String × String) := #[
  ("kernel rejected the solution", "Lean's kernel rejected a declaration that the build accepted, as a proof that \
    uses `debug.skipKernelTC` or `Lean.addDecl` allows"),
  ("theorem statement do not match", "the solution states a theorem otherwise than Challenge.lean"),
  ("constant kind don't match", "the solution declares a constant of Challenge.lean as another kind"),
  ("Const not found in solution", "the solution does not declare a theorem or hole that Challenge.lean states"),
  ("Const does not match between challenge and target", "the solution defines a constant otherwise than \
    Challenge.lean"),
  ("Solution constant is not a definition", "the solution declares a hole as something other than a definition"),
  ("Solution constant is not a theorem", "the solution declares a theorem of Challenge.lean as something else"),
  ("Illegal axiom detected", "a proof uses an axiom beyond propext, Classical.choice, and Quot.sound"),
  ("is not permitted; it is used by", "a proof uses an axiom beyond propext, Classical.choice, and Quot.sound")]

def signalled (line : String) : Bool :=
  match line.splitOn "exited with " with
  | [_, code] => (code.trimAscii.toString.toNat?.map fun code => decide (code ≥ 128)).getD false
  | _ => false

def rejection? (out : IO.Process.Output) : Option String :=
  let text := out.stdout ++ out.stderr
  let lines := text.splitOn "\n"
  if out.exitCode != 1 || lines.any signalled || lines.any (·.startsWith "bwrap:") then none
  else (rejections.find? (contains text ·.1)).map (·.2)

def compare (lake : String) (checkout config : System.FilePath) : IO IO.Process.Output := do
  let replay : IO IO.Process.Output := IO.Process.output
    { cmd := lake, args := #["comparator", "--config", config.toString], cwd := some checkout }
  let mut out ← replay
  for _ in [0:3] do
    unless contains (out.stdout ++ out.stderr) "bwrap: Can't bind mount" do break
    IO.sleep 20000
    out ← replay
  return out

def judge (lake : String) (base checkout config : System.FilePath) (statement candidate again : String) :
    IO UInt32 := do
  match ← run lake #["script", "run", "software_challenge/grade_candidate", candidate] checkout with
  | 0 => pure ()
  | 10 => return 1
  | 3 => return 3
  | code =>
    IO.eprintln s!"cannot judge: `lake script run software_challenge/grade_candidate {candidate}` exited {code} in \
      {checkout} before judging, as printed above, so grade cannot tell whether {candidate} is right. Fix the cause \
      it reports, {again}."
    return 3
  IO.FS.writeFile config statement
  let out ← compare lake checkout config
  IO.print out.stdout
  (← IO.getStdout).flush
  IO.eprint out.stderr
  if out.exitCode == 0 then
    IO.println s!"accepted: {candidate} proves every headline, kill, and witness that {base} states."
    return 0
  if let some reason := rejection? out then
    IO.eprintln s!"refused: `lake comparator` rejects {candidate}: {reason}, as printed above. Run `lake build` and \
      `lake script run software_challenge/replay` in a checkout of {candidate} to see which theorem, fix it in \
      {candidate}, {again}."
    return 1
  IO.eprintln s!"cannot judge: `lake comparator` exited {out.exitCode} without a verdict, as printed above, so \
    grade cannot tell whether {candidate} is right. Fix the cause it reports, such as `bwrap` permissions or a \
    build failure in its sandbox, {again}."
  return 3

def ownedChange (base : System.FilePath) (owned : Array String) (candidate baseRef merge again : String) :
    IO (Option UInt32) := do
  match ← run "git" (#["diff", "--quiet", candidate, "--"] ++ owned) base with
  | 0 => return none
  | 1 =>
    unless (← run "git" (#["diff", "--quiet", "HEAD", "--"] ++ owned) base) == 0 do
      discard <| run "git" (#["diff", "--stat", "HEAD", "--"] ++ owned) base
      IO.eprintln s!"cannot judge: {base} has changes to the owned files listed above that are not committed, so no \
        commit holds the statement grade would check. Commit them in {base}, {merge}, {again}."
      return some 3
    discard <| run "git" (#["diff", "--stat", candidate, "--"] ++ owned) base
    let mergeBase := firstLine (← output "git" #["merge-base", "HEAD", candidate] base).stdout
    if (← run "git" (#["diff", "--quiet", mergeBase, candidate, "--"] ++ owned) base) == 0 then
      IO.eprintln s!"refused: {baseRef} changed the owned files listed above after {candidate} branched from it, so \
        {candidate} solves an older statement. To grade it against this one, {merge}, {again}."
      return some 1
    let files := " ".intercalate <| ((← output "git" (#["diff", "--name-only", candidate, "--"] ++ owned) base).stdout
      |>.splitOn "\n").filter (!·.isEmpty)
    IO.eprintln s!"refused: {candidate} changes the owned files listed above, which state the challenge, so it is \
      not a solution of it. Restore them on {candidate} (`git checkout {candidate} && git checkout {baseRef} -- \
      {files} && git commit -m 'Restore the owned files' && git checkout {baseRef}`), {again}."
    return some 1
  | _ =>
    IO.eprintln s!"cannot judge: `git diff {candidate}` fails in {base}, as printed above, so grade cannot compare \
      the owned files. Fix what git reports, {again}."
    return some 3

def grade (candidate : String) : IO UInt32 := do
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let base ← IO.currentDir
  let again := s!"then run `lake exe grade {candidate}`"
  unless (← output "git" #["rev-parse", "--show-toplevel"] base).exitCode == 0 do
    IO.eprintln s!"cannot judge: {base} is not in a git repository, so grade cannot compare the candidate's owned \
      files with it. Run `lake exe grade {candidate}` from a git checkout of the base."
    return 3
  unless (← output "git" #["rev-parse", "--verify", "--quiet", s!"{candidate}^\{commit}"] base).exitCode == 0 do
    IO.eprintln s!"cannot judge: {candidate} names no commit of the repository at {base}, so grade cannot check it \
      out. Pass a commit or branch of that repository, as in `lake exe grade HEAD`."
    return 3
  let branch := firstLine (← output "git" #["rev-parse", "--abbrev-ref", "HEAD"] base).stdout
  let short := firstLine (← output "git" #["rev-parse", "--short", "HEAD"] base).stdout
  let baseRef := if branch == "HEAD" then short else branch
  let merge := s!"merge {baseRef} into {candidate} (`git checkout {candidate} && git merge {baseRef} && git checkout \
    {baseRef}`)"
  let some owned ← lockedFiles base | do
    IO.eprintln s!"cannot judge: {base / "owned.lock"} is missing, so grade cannot tell which files {candidate} \
      must leave unchanged. Run `lake build` in {base} to record it and commit it, {merge}, {again}."
    return 3
  unless (← run lake #["build", ":softwareChallengeStatement"] base) == 0 do
    IO.eprintln s!"cannot judge: the statement check fails in {base}, as printed above. Fix it there as it says, \
      delete owned.lock, run `lake build`, and commit; {merge}, {again}."
    return 3
  unless ← (base / "comparator.json").pathExists do
    IO.eprintln s!"cannot judge: the statement check wrote no comparator.json in {base}, so grade has no statement \
      to compare {candidate} with. Run `lake build` in {base}, {again}."
    return 3
  let statement ← IO.FS.readFile (base / "comparator.json")
  if let some code ← ownedChange base owned candidate baseRef merge again then return code
  let packages ← output lake #["script", "run", "software_challenge/grade_packages"] base
  unless packages.exitCode == 0 do
    IO.eprint packages.stderr
    IO.eprintln s!"cannot judge: `lake script run software_challenge/grade_packages` fails in {base}, as printed \
      above, so grade cannot give {candidate} the base's dependencies. Fix what it reports, {again}."
    return 3
  let prefixInRepo := firstLine (← output "git" #["rev-parse", "--show-prefix"] base).stdout
  let stamp := toString (← IO.monoNanosNow)
  let worktree := base / ".lake" / "grade" / stamp
  let config := base / ".lake" / "grade" / s!"{stamp}.json"
  IO.FS.createDirAll (base / ".lake" / "grade")
  try
    unless (← run "git" #["worktree", "add", "--detach", worktree.toString, candidate] base) == 0 do
      IO.eprintln s!"cannot judge: `git worktree add` cannot check out {candidate} at {worktree}, as printed above. \
        Run `git worktree prune` in {base}, {again}."
      return 3
    let checkout := worktree / prefixInRepo
    IO.FS.createDirAll (checkout / ".lake")
    IO.FS.writeFile (checkout / ".lake" / "package-overrides.json") packages.stdout
    judge lake base checkout config statement candidate again
  finally
    discard <| run "git" #["worktree", "remove", "--force", worktree.toString] base
    if ← worktree.pathExists then IO.FS.removeDirAll worktree
    if ← config.pathExists then IO.FS.removeFile config

end SoftwareChallenge.Grade

def main : List String → IO UInt32
  | [candidate] => SoftwareChallenge.Grade.grade candidate
  | _ => do
    IO.eprintln "usage: lake exe grade <commit> judges the candidate commit against this checkout's statement, \
      and exits 0 to accept, 1 to refuse, and 3 when it cannot judge."
    return 3

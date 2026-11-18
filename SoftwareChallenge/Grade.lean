module

public section

namespace SoftwareChallenge.Grade

def run (cmd : String) (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  (← IO.Process.spawn { cmd, args, cwd := some cwd }).wait

def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

def lockedFiles (dir : System.FilePath) : IO (Option (Array String)) := do
  let lock := dir / "owned.lock"
  unless ← lock.pathExists do return none
  return some <| #["owned.lock"] ++ ((← IO.FS.readFile lock).splitOn "\n").toArray.filterMap fun line =>
    match line.splitOn " " with
    | [_, file] => some file
    | _ => none

def verdicts : Array String := #["kernel rejected the solution", "theorem statement do not match",
  "constant kind don't match", "Const not found in solution", "Const does not match between challenge and target",
  "Solution constant is not a definition", "Solution constant is not a theorem", "Illegal axiom detected",
  "is not permitted; it is used by"]

def compare (lake : String) (checkout config : System.FilePath) : IO IO.Process.Output := do
  let replay : IO IO.Process.Output := IO.Process.output
    { cmd := lake, args := #["comparator", "--config", config.toString], cwd := some checkout }
  let mut output ← replay
  for _ in [0:3] do
    unless contains (output.stdout ++ output.stderr) "bwrap: Can't bind mount" do break
    IO.sleep 20000
    output ← replay
  return output

def grade (candidate : String) : IO UInt32 := do
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let base ← IO.currentDir
  let again := s!"then run `lake exe grade {candidate}`"
  let some owned ← lockedFiles base | do
    IO.eprintln s!"cannot judge: {base / "owned.lock"} is missing, so grade cannot tell which files {candidate} \
      must leave unchanged. Run `lake build` in {base} to record it, commit it, {again}."
    return 3
  unless (← run lake #["build", ":softwareChallengeStatement"] base) == 0 do
    IO.eprintln s!"cannot judge: the statement check fails in {base}, as printed above. Fix it there and commit, \
      {again}."
    return 3
  match ← run "git" (#["diff", "--quiet", candidate, "--"] ++ owned) base with
  | 0 => pure ()
  | 1 =>
    discard <| run "git" (#["diff", "--stat", candidate, "--"] ++ owned) base
    IO.eprintln s!"refused: {candidate} changes the owned files listed above, which state the challenge, so it is \
      not a solution of it. Restore them in {candidate} from {base}, {again}."
    return 1
  | _ =>
    IO.eprintln s!"cannot judge: `git diff {candidate}` fails in {base}, so grade cannot compare the owned files. \
      Check that {candidate} names a commit of this repository, {again}."
    return 3
  let prefixInRepo := String.ofList <| (← IO.Process.output
    { cmd := "git", args := #["rev-parse", "--show-prefix"], cwd := some base }).stdout.toList.filter (· != '\n')
  let worktree := base / ".lake" / "grade" / toString (← IO.monoNanosNow)
  IO.FS.createDirAll (base / ".lake" / "grade")
  try
    unless (← run "git" #["worktree", "add", "--detach", worktree.toString, candidate] base) == 0 do
      IO.eprintln s!"cannot judge: `git worktree add` cannot check out {candidate} at {worktree}. Run \
        `git worktree prune` in {base}, {again}."
      return 3
    match ← run lake #["script", "run", "software_challenge/grade_candidate", candidate] (worktree / prefixInRepo) with
    | 0 => pure ()
    | 1 => return 1
    | _ => return 3
    let output ← compare lake (worktree / prefixInRepo) (base / "comparator.json")
    IO.print output.stdout
    IO.eprint output.stderr
    if output.exitCode == 0 then
      IO.println s!"accepted: {candidate} proves every headline, kill, and witness that {base} states."
      return 0
    if output.exitCode == 1 && verdicts.any (contains (output.stdout ++ output.stderr) ·) then
      IO.eprintln s!"refused: `lake comparator` rejects {candidate}, as printed above. Fix what it reports in \
        {candidate}, {again}."
      return 1
    IO.eprintln s!"cannot judge: `lake comparator` exited {output.exitCode} without a verdict, as printed above, so \
      grade cannot tell whether {candidate} is right. Fix the cause it reports, such as `bwrap` permissions or a \
      build failure in its sandbox, {again}."
    return 3
  finally
    discard <| run "git" #["worktree", "remove", "--force", worktree.toString] base
    if ← worktree.pathExists then IO.FS.removeDirAll worktree

end SoftwareChallenge.Grade

def main : List String → IO UInt32
  | [candidate] => SoftwareChallenge.Grade.grade candidate
  | _ => do
    IO.eprintln "usage: lake exe grade <commit> judges the candidate commit against this checkout's statement, \
      and exits 0 to accept, 1 to refuse, and 3 when it cannot judge."
    return 3

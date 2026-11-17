module

public section

namespace SoftwareChallenge.Grade

def run (cmd : String) (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  (← IO.Process.spawn { cmd, args, cwd := some cwd }).wait

def ownedFiles (dir : System.FilePath) : IO (Array String) := do
  let report ← IO.FS.readFile (dir / ".lake" / "build" / "softwareChallenge.txt")
  let some line := (report.splitOn "\n").find? (·.startsWith "Owned: ")
    | throw <| IO.userError s!"{dir} reports no owned files"
  return ((line.splitOn " ").drop 1).toArray

def audited (lake : String) (dir : System.FilePath) : IO Bool := do
  return (← run lake #["build"] dir) == 0 && (← run lake #["build", ":softwareChallenge"] dir) == 0

def grade (candidate : String) : IO UInt32 := do
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let base ← IO.currentDir
  let prefixInRepo := String.ofList <| (← IO.Process.output
    { cmd := "git", args := #["rev-parse", "--show-prefix"], cwd := some base }).stdout.toList.filter (· != '\n')
  unless ← audited lake base do
    IO.eprintln "cannot grade: the base does not pass"; return 3
  let owned ← ownedFiles base
  match ← run "git" (#["diff", "--quiet", candidate, "--"] ++ owned) base with
  | 0 => pure ()
  | 1 =>
    discard <| run "git" (#["diff", "--stat", candidate, "--"] ++ owned) base
    IO.eprintln s!"refused: {candidate} changes files the owner decides"; return 1
  | _ => IO.eprintln s!"cannot grade: git cannot compare {candidate}"; return 3
  let scratch ← IO.FS.createTempDir
  let worktree := scratch / "candidate"
  let checkout := worktree / prefixInRepo
  try
    unless (← run "git" #["worktree", "add", "--detach", worktree.toString, candidate] base) == 0 do
      return 3
    unless ← audited lake checkout do return 1
    unless (← ownedFiles checkout) == owned do
      IO.eprintln s!"refused: {candidate} adds files the owner decides"; return 1
    if (← run lake #["test"] checkout) == 0 then return 0 else return 1
  finally
    discard <| run "git" #["worktree", "remove", "--force", worktree.toString] base
    IO.FS.removeDirAll scratch

end SoftwareChallenge.Grade

def main : List String → IO UInt32
  | [candidate] => SoftwareChallenge.Grade.grade candidate
  | _ => do IO.eprintln "usage: lake exe grade <candidate commit>"; return 3

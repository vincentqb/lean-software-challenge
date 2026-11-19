module

public meta import SoftwareChallenge.Read
public meta import SoftwareChallenge.Steps.Comparator
public meta import SoftwareChallenge.Steps.Schedule

public section
meta section

open Lean

namespace SoftwareChallenge.Steps.Replay

def again : String := "then run `lake script run software_challenge/replay`"

def names (token short : String) : Bool :=
  token == short || token.endsWith ("." ++ short)

def tokensOf (line : String) : List String :=
  (line.splitOn " ").filter (!·.isEmpty)

def killed (line : String) : Option String :=
  match (tokensOf line).dropWhile (· != "@[kills") with
  | _ :: written :: _ => (((written.splitOn "]").headD "").splitOn ",").head?
  | _ => none

def lineOf (challenge : String) (name : Name) : Option String :=
  let short := match name with
    | .str _ last => last
    | _ => toString name
  let lines := (challenge.splitOn "\n").zipIdx
  let declared := lines.findSome? fun (line, index) =>
    if (tokensOf line).any (names · short) && line.contains "theorem " then some (index + 1) else none
  let derivedFrom := if short.endsWith "_applies" then some (short.dropEnd "_applies".length).toString else none
  let firstKill := derivedFrom.bind fun headline => lines.findSome? fun (line, index) =>
    if (killed line).any (names · headline) then some (index + 1) else none
  ((declared.orElse fun _ => firstKill).map fun line => s!" (Challenge.lean:{line})")

def explain (solution : Name) (place : String) (name : Name) (output : IO.Process.Output) : String :=
  let shown := s!"{output.stdout}{output.stderr}"
  match Comparator.rejection? output.exitCode shown with
  | some rejection => s!"`lake comparator` rejects {name}{place}: {Comparator.reason rejection}. \
      {Comparator.remedy solution rejection}, {again}.\n{shown}"
  | none => s!"`lake comparator` could not check {name}{place}: it exited {output.exitCode} without a verdict \
      ({Comparator.failure output}). Fix that cause, such as a dependency under /home, /root, /run, /tmp, or /var, \
      which its sandbox hides, {again}.\n{shown}"

def lineFor (name : Name) (output : IO.Process.Output) (elapsed : Nat) : String :=
  let text := output.stdout ++ output.stderr
  if output.exitCode == 0 then s!"{name}  {tenths elapsed}"
  else if (Comparator.rejection? output.exitCode text).isSome then s!"{name}  {tenths elapsed}  (rejected)"
  else s!"{name}  {tenths elapsed}  (could not run, exit {output.exitCode})"

def run (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .replay
  let some text ← Read.readInput lake Read.comparatorFile .replay | do
    IO.eprintln s!"{Read.comparatorFile}:1: comparator.json is missing, but replay reads the statement from it. \
      `lake build` writes it from Challenge.lean: run `lake build`, {again}."
    return 1
  let some config := Config.parse text | do
    IO.eprintln s!"{Read.comparatorFile}:1: {Read.comparatorProblem}, so replay cannot tell which theorems to check. \
      Delete comparator.json and run `lake build`, {again}."
    return 2
  let challenge ← match Read.challengeOf? lake with
    | some candidate => Read.readSource lake candidate.file .replay
    | none => pure ""
  let dir := (lakeFile.parent.getD ".") / "comparator"
  IO.FS.createDirAll dir
  let lakeCommand := (← IO.getEnv "LAKE").getD "lake"
  let start ← IO.monoMsNow
  let results ← schedule (← jobsAllowed) config.theorems.zipIdx fun (name, index) =>
    Comparator.run lakeCommand lake.packageDir (dir / s!"{index}.json") { config with theorems := #[name] }
  let total := (← IO.monoMsNow) - start
  let done := (config.theorems.zip results).qsort fun left right => left.2.2 > right.2.2
  for (name, output, _) in done do
    unless output.exitCode == 0 do IO.eprintln (explain config.solution ((lineOf challenge name).getD "") name output)
  let accepted := (done.filter (·.2.1.exitCode == 0)).size
  let report := (done.map fun (name, output, elapsed) => lineFor name output elapsed).push
    s!"Replayed: {accepted} of {config.theorems.size} theorems in {tenths total}"
  (← IO.getStderr).flush
  IO.println ("\n".intercalate report.toList)
  if done.any fun (_, output, _) => (Comparator.rejection? output.exitCode (output.stdout ++ output.stderr)).isSome then
    return 1
  return if done.any (·.2.1.exitCode != 0) then 2 else 0

end SoftwareChallenge.Steps.Replay

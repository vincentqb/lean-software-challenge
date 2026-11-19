module

public import SoftwareChallenge.CoreCode.Grade
public import SoftwareChallenge.CoreCode.Format

public section

namespace SoftwareChallenge.Steps.Comparator

def run (lake : String) (dir configFile : System.FilePath) (config : Config) : IO IO.Process.Output := do
  let attempt : IO IO.Process.Output := do
    IO.FS.writeFile configFile (Config.render config)
    IO.Process.output
      { cmd := lake, args := #["comparator", "--config", configFile.toString], cwd := some dir }
  let mut output ← attempt
  for _ in [0:3] do
    unless Comparator.retryable output.exitCode (output.stdout ++ output.stderr) do break
    IO.sleep 20000
    output ← attempt
  return output

end SoftwareChallenge.Steps.Comparator

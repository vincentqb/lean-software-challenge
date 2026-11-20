module

public meta import SoftwareChallenge.Steps.Statement
public meta import SoftwareChallenge.Steps.Lint
public meta import SoftwareChallenge.Steps.Test
public meta import SoftwareChallenge.Steps.Replay
public meta import SoftwareChallenge.Steps.Facts

public section
meta section

namespace SoftwareChallenge.Steps

def usage : String :=
  "usage: `lean --run SoftwareChallengeRun.lean <step> <lake.json>`, where <step> is statement, lint, test, replay, \
    facts or drive; the lakefile of software_challenge runs it from `lake build`, `lake lint` and `lake test`."

def dispatch (step : String) (lakeFile : System.FilePath) (args : List String) : IO UInt32 :=
  match step, args with
  | "statement", ["importers"] => Statement.importers lakeFile
  | "statement", _ => Statement.run lakeFile args
  | "lint", ["importers"] => Lint.importers lakeFile
  | "lint", _ => Lint.run lakeFile
  | "drive", _ => Lint.drive lakeFile
  | "test", loads => Test.run lakeFile loads.toArray
  | "replay", _ => Replay.run lakeFile
  | "facts", _ => Facts.run lakeFile
  | _, _ => do IO.eprintln usage; return 3

def run : List String → IO UInt32
  | step :: lakeFile :: args => do
    let code ← try dispatch step lakeFile args catch failure => do IO.eprintln (toString failure); pure 3
    IO.FS.writeFile ((System.FilePath.mk lakeFile).parent.getD "." / s!"{step}.status") (toString code)
    return code
  | _ => do IO.eprintln usage; return 3

end SoftwareChallenge.Steps

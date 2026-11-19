module

public meta import SoftwareChallenge.Read

public section
meta section

open Lean

namespace SoftwareChallenge.Steps.Facts

def run (lakeFile : System.FilePath) : IO UInt32 := do
  IO.println (reprStr (← Read.readFacts (← Read.loadLake lakeFile .lint) .lint))
  return 0

end SoftwareChallenge.Steps.Facts

module

public meta import SoftwareChallenge.Read
public meta import SoftwareChallenge.CoreCode.Rules.Lint
public meta import SoftwareChallenge.Steps.Statement

public section
meta section

open Lean

namespace SoftwareChallenge.Steps.Lint

def run (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let result := SoftwareChallenge.Lint.run (← Read.readFacts lake .lint)
  IO.println ("\n".intercalate result.report.toList)
  return result.code

def importers (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let some candidate := Read.challengeOf? lake | return 3
  let facts : Facts := { (default : Facts) with lake, challenge := Read.emptyChallenge candidate.module candidate.file }
  let lines ← challengeImports lake .lint
  if lines.isEmpty then return 3
  IO.println (errorListing (lines.map fun line => Report.item ((Lint.Error.importsChallenge line).message facts))
    "lake lint" .lint)
  return 1

end SoftwareChallenge.Steps.Lint

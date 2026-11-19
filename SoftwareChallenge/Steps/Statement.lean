module

public meta import SoftwareChallenge.Read
public meta import SoftwareChallenge.CoreCode.Rules.Statement
public meta import SoftwareChallenge.CoreCode.Report.StatementMessages
public meta import SoftwareChallenge.CoreCode.Report.Report

public section
meta section

open Lean

namespace SoftwareChallenge.Steps

def distinct (items : Array String) : Array String :=
  items.foldl (fun kept item => if kept.contains item then kept else kept.push item) #[]

def errorListing (items : Array String) (step : String) (next : Next) : String :=
  let items := distinct items
  let count := s!"{items.size} {if items.size == 1 then "error" else "errors"}"
  s!"{Report.listing "Errors" items}\n{step} found {count}, as listed under Errors above, so \
    `{next.command}` fails. Fix each as it says, then run `{next.command}`."

def challengeImports (lake : LakeFacts) (next : Next) : IO (Array ImportLine) := do
  let some candidate := Read.challengeOf? lake | return #[]
  lake.modules.flatMapM fun source => do
    let lines ← Read.importLines source.module source.file (← Read.readSource lake source.file next)
    return lines.filter (·.fact.name == candidate.module)

namespace Statement

def challengeOf (lake : LakeFacts) (compiled : List String) : IO ChallengeFacts := do
  let (some candidate, [dir]) := (Read.challengeOf? lake, compiled) | return Read.emptyChallenge .anonymous ""
  searchPathRef.modify (System.FilePath.mk dir :: ·)
  let imported ← Read.challengeEnv { lake with challengeCandidates := #[] } candidate.module .build
  Read.listedChallenge lake candidate imported .build

def written (lake : LakeFacts) (file : String) (text : String) : IO Bool := do
  if (← Read.readInput lake file .build) == some text then return false
  IO.FS.writeFile (Read.pathIn lake file) text
  return true

def perform (lake : LakeFacts) (writes : Statement.Writes) : IO (Array String) := do
  let mut lines := #[]
  if let some config := writes.config? then
    if ← written lake Read.comparatorFile (Config.render config) then
      lines := lines.push (Statement.wroteComparator config)
  if let some entries := writes.lock? then
    if ← written lake Read.lockFile (Lock.render entries) then
      lines := lines.push (Statement.recordedLock entries)
  return lines

def failed (lake : LakeFacts) : IO UInt32 := do
  let file := ((Read.challengeOf? lake).map (·.file)).getD "Challenge.lean"
  IO.println (errorListing #[Report.item (Statement.Error.message lake default default (.challengeFails file))]
    "The statement check" .build)
  return 1

def run (lakeFile : System.FilePath) (args : List String) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .build
  if args == ["failed"] then return ← failed lake
  let files ← Read.fileFacts lake .build
  let challenge ← challengeOf lake args
  let result := SoftwareChallenge.Statement.run lake files challenge
  if result.code == 0 then
    for line in ← perform lake result.writes do IO.println line
  else
    IO.println (errorListing (result.setup.map (fun setup => Report.item (setup.message lake)) ++
      result.errors.map fun error => Report.item (error.message lake files challenge)) "The statement check" .build)
  return result.code

def importers (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .build
  let some candidate := Read.challengeOf? lake | return 3
  let challenge := Read.emptyChallenge candidate.module candidate.file
  let lines ← challengeImports lake .build
  if lines.isEmpty then return 3
  IO.println (errorListing (lines.map fun line =>
    Report.item ((Statement.Error.importsChallenge line).message lake default challenge)) "The statement check" .build)
  return 1

end Statement

end SoftwareChallenge.Steps

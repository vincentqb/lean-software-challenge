module

public meta import Lean
public meta import SoftwareChallenge.CoreCode.Facts
public meta import SoftwareChallenge.CoreCode.Format
public meta import SoftwareChallenge.Read.Source

public section
meta section

open Lean

namespace SoftwareChallenge.Read

def lockFile : String := "owned.lock"

def comparatorFile : String := "comparator.json"

def pathIn (lake : LakeFacts) (path : String) : System.FilePath :=
  System.FilePath.mk lake.packageDir / path

def named (lake : LakeFacts) (path : String) : Bool :=
  lake.inputs.contains path || lake.modules.any (·.file == path) || lake.challengeCandidates.any (·.file == path)

private def readIfPresent (file : System.FilePath) : IO (Option String) := do
  unless ← file.pathExists do return none
  return some (← IO.FS.readFile file)

def readInput (lake : LakeFacts) (path : String) : IO (Option String) := do
  unless lake.inputs.contains path do
    throw <| .userError s!"{path}: lake.json does not list it among the inputs, so the step may not read it, and \
      its result would not be traced. List {path} in the inputs that the facet in lakefile.lean writes to lake.json, \
      then run `lake build`."
  readIfPresent (pathIn lake path)

def readSource (lake : LakeFacts) (path : String) : IO String := do
  unless named lake path do
    throw <| .userError s!"{path}: lake.json names it neither as an input nor as a module's file, so the step may \
      not read it. Name it in the modules or inputs that the facet in lakefile.lean writes to lake.json, then run \
      `lake build`."
  return (← readIfPresent (pathIn lake path)).getD ""

def digestOf (text : String) : String := toString (hash text)

def decode {α : Type} (text? : Option String) (parse : String → Option α) (problem : String) : Decoded α :=
  match text? with
  | none => .missing
  | some text => match parse text with
    | some value => .decoded value
    | none => .unreadable problem

def lockProblem : String :=
  s!"{lockFile} is not a JSON object from each owned path to its digest, as `lake build` records it"

def comparatorProblem : String :=
  s!"{comparatorFile} is not the JSON object of challenge_module, solution_module, theorem_names, \
    definition_names and permitted_axioms that `lake build` writes"

def fileFacts (lake : LakeFacts) : IO FileFacts := do
  let digested := lake.inputs.filter fun path => path != lockFile && path != comparatorFile
  return {
    lock := decode (← readInput lake lockFile) Lock.parse lockProblem
    comparator := decode (← readInput lake comparatorFile) Config.parse comparatorProblem
    digests := ← digested.filterMapM fun path => do
      return (← readInput lake path).map fun text => { path, digest := digestOf text } }

def importLines (module : Name) (file source : String) : IO (Array ImportLine) := do
  let context := Parser.mkInputContext source file
  let (header, _, _) ← Parser.parseHeader context
  let written := header.raw[2].getArgs
  return (Elab.HeaderSyntax.imports header (includeInit := false)).zipIdx.map fun (found, index) =>
    let line := ((written[index]?.bind (·.getPos?)).map (context.fileMap.toPosition · |>.line)).getD 0
    { module, fact := { name := found.module, comptime := found.isMeta, line }, text := lineAt source line }

def placedImports (module : Name) (data : ModuleData) (written : Array ImportLine) : Array ImportLine :=
  data.imports.map fun dependency =>
    match written.find? fun line => line.fact.name == dependency.module && line.fact.comptime == dependency.isMeta with
    | some line => line
    | none => { module, fact := { name := dependency.module, comptime := dependency.isMeta, line := 0 }, text := "" }

end SoftwareChallenge.Read

module

public import SoftwareChallenge.CoreSpec.Grade
public import SoftwareChallenge.CoreSpec.Format

public section

namespace SoftwareChallenge

def Grade.decide (observations : List Observation) : Verdict :=
  match observations.find? (·.verdict != .accept) with
  | some stopped => stopped.verdict
  | none => if observations.map (·.stage) = Stage.order then .accept else .cannotJudge

namespace Comparator

inductive Rejection where
  | kernel | statement | kind | absent | unexported | differs | notDefinition | notTheorem | axiomUsed
  | missing (name : String)
  deriving DecidableEq

def rejections : List (String × Rejection) := [
  ("kernel rejected the solution", .kernel),
  ("Challenge and solution theorem statement do not match", .statement),
  ("Challenge and solution constant kind don't match", .kind),
  ("Const not found in solution", .absent),
  ("Constant not found in solution", .unexported),
  ("Const does not match between challenge and target", .differs),
  ("Solution constant is not a definition", .notDefinition),
  ("Solution constant is not a theorem", .notTheorem),
  ("Illegal axiom detected", .axiomUsed),
  ("is not permitted; it is used by", .axiomUsed)]

def lines (output : String) : List String :=
  (output.splitOn "\n").map (·.trimAscii.toString)

def signalled (line : String) : Bool :=
  match line.splitOn "exited with " with
  | [_, code] => (((code.splitOn " ").getLast?.bind (·.toNat?)).map fun code => decide (code ≥ 128)).getD false
  | _ => false

def missingConstant? (output : String) : Option String :=
  (lines output).findSome? fun line =>
    if line.startsWith "PANIC at LeanExport" then
      match line.splitOn ": Constant " with
      | [_, rest] =>
        match rest.splitOn " not found in environment" with
        | [name, _] => some name
        | _ => none
      | _ => none
    else none

def rejection? (code : UInt32) (output : String) : Option Rejection :=
  if code != 1 || (lines output).any (·.startsWith "bwrap:") then none
  else match missingConstant? output with
    | some name => some (.missing name)
    | none =>
      if (lines output).any signalled then none
      else (rejections.find? (output.contains ·.1)).map (·.2)

def classify (code : UInt32) (output : String) : Verdict :=
  if code == 0 then .accept
  else if (rejection? code output).isSome then .refuse
  else .cannotJudge

def retryable (code : UInt32) (output : String) : Bool :=
  code != 0 && output.contains "bwrap: Can't bind mount"

end Comparator

namespace Sandbox

def components (path : String) : List String :=
  (path.splitOn "/").filter fun part => !part.isEmpty && part != "."

def within (path root : String) : Bool :=
  (components root).isPrefixOf (components path)

def coveredRoots : List String := ["/home", "/root", "/run", "/tmp", "/var"]

def covers (dir : String) : Bool :=
  coveredRoots.any (within dir ·)

end Sandbox

def Grade.pathspec (path : List String) : String :=
  ":(top,literal)" ++ "/".intercalate path

def Grade.ownedPathspecs (packagePrefix : String) (lock : Array Lock.Entry) : Array String :=
  ((lock.map (·.path)).push "owned.lock").map fun path =>
    Grade.pathspec (Sandbox.components packagePrefix ++ Sandbox.components path)

end SoftwareChallenge

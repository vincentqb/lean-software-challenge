module

public import SoftwareChallenge.CoreSpec.Grade
public import SoftwareChallenge.CoreSpec.Format

public section

namespace SoftwareChallenge

open Lean

def Grade.decide (observations : List Observation) : Verdict :=
  match observations.find? (·.verdict != .accept) with
  | some stopped => stopped.verdict
  | none => if observations.map (·.stage) = Stage.order then .accept else .cannotJudge

namespace Comparator

inductive Rejection where
  | kernel | statement | kind | absent | unexported | differs | notDefinition | notTheorem | axiomUsed | unbuilt
  deriving DecidableEq, Repr, Inhabited

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

def progressPrefixes : List String := ["Resolving dependencies", "Building ", "Exporting ", "Running "]

def lines (output : String) : List String :=
  (output.splitOn "\n").map (·.trimAscii.toString)

def signalled (line : String) : Bool :=
  match line.splitOn "exited with " with
  | [_, code] => (code.trimAscii.toString.toNat?.map fun code => decide (code ≥ 128)).getD false
  | _ => false

def toolchainFailed (output : String) : Bool :=
  output.contains "external command '"

def blocked (output : String) : Bool :=
  (lines output).any (fun line => line.startsWith "bwrap:" || signalled line) ||
    output.toLower.contains "read-only file system" || toolchainFailed output

def lastProgress? (output : String) : Option String :=
  ((lines output).filter fun line => progressPrefixes.any fun progress => line.startsWith progress).getLast?

def rejection? (solution : Name) (code : UInt32) (output : String) : Option Rejection :=
  if code != 1 || blocked output then none
  else match rejections.find? (output.contains ·.1) with
    | some (_, rejection) => some rejection
    | none =>
      if lastProgress? output == some s!"Building {solution}" && output.contains "Child exited with" then
        some .unbuilt
      else none

def classify (solution : Name) (code : UInt32) (output : String) : Verdict :=
  if code == 0 then .accept
  else if (rejection? solution code output).isSome then .refuse
  else .cannotJudge

def retryable (code : UInt32) (output : String) : Bool :=
  code != 0 && output.contains "bwrap: Can't bind mount"

def primitiveTargets : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble,
  ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
  ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char, ``optParam, ``autoParam, ``semiOutParam,
  ``outParam]

def exportTargets (config : Config) : Array Name :=
  let quotient := if config.axioms.contains ``Quot.sound then #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] else #[]
  quotient ++ config.theorems ++ config.axioms ++ primitiveTargets ++ config.definitions

end Comparator

namespace Sandbox

def components (path : String) : List String :=
  (path.splitOn "/").filter fun part => !part.isEmpty && part != "."

def within (path root : String) : Bool :=
  (components root).isPrefixOf (components path)

def coveredRoots : List String := ["/home", "/root", "/run", "/tmp", "/var"]

def covers (dir : String) : Bool :=
  coveredRoots.any (within dir ·)

inductive Placement where
  | ok | hidden | insideRepository
  deriving DecidableEq, Repr, Inhabited

structure Dependency where
  name : Name
  dir : String
  placement : Placement
  deriving DecidableEq, Repr, Inhabited

def placement (packageDir : String) (repository? : Option String) (dir : String) : Placement :=
  if within dir packageDir then .ok
  else if covers dir then .hidden
  else match repository? with
    | some repository =>
      if within dir repository && !((components dir).drop (components repository).length).contains ".lake" then
        .insideRepository
      else .ok
    | none => .ok

def classify (packageDir : String) (repository? : Option String) (packages : Array (Name × String)) :
    Array Dependency :=
  packages.map fun (name, dir) => { name, dir, placement := placement packageDir repository? dir }

end Sandbox

def Grade.pathspec (path : List String) : String :=
  ":(top,literal)" ++ "/".intercalate path

def Grade.exclusion (path : List String) : String :=
  ":(top,literal,exclude)" ++ "/".intercalate path

def Grade.ownedPathspecs (packagePrefix repositoryDir : String) (lock : Array Lock.Entry)
    (dependencies : Array Sandbox.Dependency) : Array (Array String) :=
  let package := Sandbox.components packagePrefix
  let files := ((lock.map (·.path)).push "owned.lock").map fun path =>
    Grade.pathspec (package ++ Sandbox.components path)
  let directories := (dependencies.filter (·.placement == .insideRepository)).filterMap fun dependency =>
    let relative := (Sandbox.components dependency.dir).drop (Sandbox.components repositoryDir).length
    if relative == package then none
    else if relative.isPrefixOf package then some #[Grade.pathspec relative, Grade.exclusion package]
    else some #[Grade.pathspec relative]
  #[files] ++ directories

end SoftwareChallenge

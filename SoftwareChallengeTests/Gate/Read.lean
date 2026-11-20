module

public meta import SoftwareChallenge.Read
public meta import SoftwareChallenge.CoreCode.Rules.Lint
public meta import SoftwareChallengeTests.Golden.ConstantFolding

public section
meta section

open Lean SoftwareChallenge

namespace SoftwareChallengeTests.Gate.Read

def source (module : Name) : SourceFact :=
  { module, file := module.toString.replace "." "/" ++ ".lean" }

def casesLake (dir : String) (modules : Array Name) : LakeFacts :=
  { packageDir := dir, configFiles := #["lakefile.lean"], modules := modules.map source,
    challengeCandidates := #[source `Challenge], defaultExeRoots := #[], packages := #[], defaultTargets := #[`Cases],
    builtinLint := none, testDriver := "software_challenge/test_challenge", testDriverArgs := #[],
    testDriverArgsPlace := { file := "lakefile.lean", line := 1 }, ownTests := #[],
    inputs := #["owned.lock", "comparator.json"] }

def verdicts (dir : String) (modules : List String) : IO UInt32 := do
  let facts ← SoftwareChallenge.Read.readFacts (casesLake dir (modules.toArray.map String.toName)) .lint
  for target in facts.challenge.targets do
    IO.println s!"{target.constant.name} {if (facts.solution.standingOf target).proved then "accept" else "refuse"}"
  return 0

def report : IO UInt32 := do
  for line in (Lint.run SoftwareChallengeTests.Golden.constantFolding).report do IO.println line
  return 0

def usage : String :=
  "usage: `lake env lean --run SoftwareChallengeTests/Gate/Read.lean report` prints the lint report of the golden \
    facts, and `… comparator <dir> <module>…` prints the standing rule's verdict on each theorem and hole of the \
    package at <dir> whose default target builds those modules; `lake exe lsc-gate` runs both."

end SoftwareChallengeTests.Gate.Read

def main : List String → IO UInt32
  | ["report"] => SoftwareChallengeTests.Gate.Read.report
  | "comparator" :: dir :: modules => SoftwareChallengeTests.Gate.Read.verdicts dir modules
  | _ => do IO.eprintln SoftwareChallengeTests.Gate.Read.usage; return 2

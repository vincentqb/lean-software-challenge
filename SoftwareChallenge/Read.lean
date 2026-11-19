module

public meta import SoftwareChallenge.Read.Lake
public meta import SoftwareChallenge.Read.Files
public meta import SoftwareChallenge.Read.Environment
public meta import SoftwareChallenge.Read.Challenge
public meta import SoftwareChallenge.Read.Inventory
public meta import SoftwareChallenge.Read.Checks
public meta import SoftwareChallenge.Read.Solution
public meta import SoftwareChallenge.Read.Census

public section
meta section

open Lean

namespace SoftwareChallenge.Read

def challengeOf? (lake : LakeFacts) : Option SourceFact :=
  match lake.challengeCandidates with
  | #[candidate] => some candidate
  | _ => none

def readChallenge (lake : LakeFacts) : IO ChallengeFacts := do
  let some candidate := challengeOf? lake | return emptyChallenge .anonymous ""
  let env ← challengeEnv lake candidate.module
  let challenge ← challengeFacts lake candidate env
  requireChallengeCensus env challenge
  return challenge

def readSolution (lake : LakeFacts) (challenge : ChallengeFacts) : IO SolutionFacts := do
  let env ← catalogEnv lake challenge.module
  let solution ← solutionFacts lake challenge env
  requireCatalogCensus env lake (catalog lake challenge.module) solution
  return solution

def readStatement (lake : LakeFacts) : IO (FileFacts × ChallengeFacts) :=
  return (← fileFacts lake, ← readChallenge lake)

def readFacts (lake : LakeFacts) : IO Facts := do
  let challenge ← readChallenge lake
  return { lake, files := ← fileFacts lake, challenge, solution := ← readSolution lake challenge }

end SoftwareChallenge.Read

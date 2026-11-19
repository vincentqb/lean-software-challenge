module

public meta import SoftwareChallenge.Read.Lake
public meta import SoftwareChallenge.Read.Files
public meta import SoftwareChallenge.Read.Environment
public meta import SoftwareChallenge.Read.Challenge
public meta import SoftwareChallenge.Read.Inventory
public meta import SoftwareChallenge.Read.Checks
public meta import SoftwareChallenge.Read.SolutionFacts
public meta import SoftwareChallenge.Read.Census

public section
meta section

open Lean

namespace SoftwareChallenge.Read

def challengeOf? (lake : LakeFacts) : Option SourceFact :=
  match lake.challengeCandidates with
  | #[candidate] => some candidate
  | _ => none

def readChallenge (lake : LakeFacts) (next : Next) : IO ChallengeFacts := do
  let some candidate := challengeOf? lake | return emptyChallenge .anonymous ""
  let env ← challengeEnv lake candidate.module next
  let challenge ← challengeFacts lake candidate env next
  requireChallengeCensus env challenge next
  return challenge

def readSolution (lake : LakeFacts) (challenge : ChallengeFacts) (next : Next) : IO SolutionFacts := do
  let imported ← catalogEnv lake challenge.module next
  let solution ← solutionFacts lake challenge imported next
  requireCatalogCensus imported lake (catalog lake challenge.module) solution next
  return solution

def readStatement (lake : LakeFacts) (next : Next) : IO (FileFacts × ChallengeFacts) :=
  return (← fileFacts lake next, ← readChallenge lake next)

def readFacts (lake : LakeFacts) (next : Next) : IO Facts := do
  let challenge ← readChallenge lake next
  return { lake, files := ← fileFacts lake next, challenge, solution := ← readSolution lake challenge next }

end SoftwareChallenge.Read

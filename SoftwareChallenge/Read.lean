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

def readOwned (lake : LakeFacts) (challenge : ChallengeFacts) (next : Next) : IO OwnedFacts := do
  if (Statement.ownedRoots lake challenge).isEmpty then return {}
  ownedFacts lake challenge.module (← ownedEnv lake challenge next) next

def listedChallenge (lake : LakeFacts) (candidate : SourceFact) (imported : Imported) (next : Next) :
    IO ChallengeFacts := do
  let challenge ← challengeFacts lake candidate imported next
  requireChallengeCensus imported.env challenge next
  requireClosureCensus lake challenge next
  return { challenge with owned := ← readOwned lake challenge next }

def readSolution (lake : LakeFacts) (challenge : ChallengeFacts) (next : Next) : IO SolutionFacts := do
  let imported ← catalogEnv lake challenge.module next
  let solution ← solutionFacts lake challenge imported next
  requireCatalogCensus imported lake (catalog lake challenge.module) solution next
  return solution

def readListedChallenge (lake : LakeFacts) (next : Next) : IO ChallengeFacts := do
  let some candidate := challengeOf? lake | return emptyChallenge .anonymous ""
  listedChallenge lake candidate (← challengeEnv lake candidate.module next) next

def readFacts (lake : LakeFacts) (next : Next) : IO Facts := do
  let challenge ← readListedChallenge lake next
  return { lake, files := ← fileFacts lake next, challenge, solution := ← readSolution lake challenge next }

end SoftwareChallenge.Read

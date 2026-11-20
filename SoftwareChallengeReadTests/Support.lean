module

public meta import SoftwareChallenge.Read

public section
meta section

open Lean SoftwareChallenge SoftwareChallenge.Read

namespace SoftwareChallengeReadTests

def fixture (name : Name) : Name := `SoftwareChallengeTests.Fixtures ++ name

def contains (text fragment : String) : Bool := (text.splitOn fragment).length > 1

def lakeOf (modules : Array Name) (challenge? : Option Name := none) (inputs : Array String := #[]) :
    IO LakeFacts := do
  return {
    packageDir := (← IO.currentDir).toString, configFiles := #["lakefile.lean"]
    modules := modules.map fun module => ⟨module, sourcePath module⟩
    challengeCandidates := (challenge?.map fun module => #[⟨module, sourcePath module⟩]).getD #[]
    defaultExeRoots := #[], packages := #[], defaultTargets := #[`statement], builtinLint := none, testDriver := "software_challenge/test_challenge"
    testDriverArgs := #[], testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, ownTests := #[], inputs }

def readChallenge (lake : LakeFacts) (next : Next) : IO ChallengeFacts := do
  let some candidate := challengeOf? lake | return emptyChallenge .anonymous ""
  let imported ← challengeEnv lake candidate.module next
  let challenge ← challengeFacts lake candidate imported next
  requireChallengeCensus imported.env challenge next
  return challenge

def challengeNamed (module : Name) : IO ChallengeFacts := do
  readChallenge (← lakeOf #[] (some module)) .lint

def headlineNamed? (challenge : ChallengeFacts) (name : Name) : Option HeadlineFact :=
  challenge.headlines.find? (·.target.constant.name == name)

def declarationNamed? (inventory : Inventory) (module name : Name) : Option DeclarationFact :=
  inventory.declarations.find? fun fact => fact.module == module && fact.name == name

def refusal (action : IO Unit) : IO (Option String) :=
  try action; pure none catch failure => pure (some (toString failure))

def check (holds : Bool) (failure : String) : IO Unit := do
  unless holds do throw <| .userError failure

end SoftwareChallengeReadTests

module

public meta import Lean
public meta import SoftwareChallenge.CoreCode.Facts
public meta import SoftwareChallenge.Read.Source
public meta import SoftwareChallenge.Read.Environment

public section
meta section

open Lean

namespace SoftwareChallenge.Read

def challengeRecorded (challenge : ChallengeFacts) : NameSet :=
  let targets := challenge.targets.flatMap fun target => #[target.constant.name] ++ target.auxiliaries.map (·.name)
  NameSet.ofList (targets ++ challenge.filled.map (·.1) ++ challenge.axioms.map (·.1)).toList

def challengeMisses (env : Environment) (challenge : ChallengeFacts) : Array Name :=
  match moduleData? env challenge.module with
  | some (_, data) =>
    let recorded := challengeRecorded challenge
    data.constNames.filter (!recorded.contains ·)
  | none => #[]

def catalogMisses (imported : Imported) (modules : Array Name) (solution : SolutionFacts) : Array (Name × Name) :=
  let recorded : Std.HashSet (Name × Name) :=
    Std.HashSet.ofArray (solution.inventory.declarations.map fun fact => (fact.module, fact.name))
  modules.flatMap fun module =>
    if !solution.inventory.modules.any (·.name == module) then #[(module, .anonymous)] else
      match imported.compiled? module with
      | some (_, data) => (data.constNames.filter fun name => !recorded.contains (module, name)).map (module, ·)
      | none => #[(module, .anonymous)]

def censusMessage (file : String) (module : Name) (missed : Array Name) (next : Next) : String :=
  let listed := if missed.all (·.isAnonymous) then "the module itself" else
    ", ".intercalate ((missed.filter (!·.isAnonymous)).map toString).toList
  s!"{file}:1: the facts the step read miss {listed}, which the compiled {module} holds, so the step cannot judge \
    the package: SoftwareChallenge.Read must record every constant it is shown, and no edit to the package fixes \
    this. Fix SoftwareChallenge/Read so that it records them, then run `{next.command}`."

def requireChallengeCensus (env : Environment) (challenge : ChallengeFacts) (next : Next) : IO Unit := do
  let missed := challengeMisses env challenge
  unless missed.isEmpty do throw <| .userError (censusMessage challenge.file challenge.module missed next)

def requireCatalogCensus (imported : Imported) (lake : LakeFacts) (modules : Array Name) (solution : SolutionFacts)
    (next : Next) : IO Unit := do
  let missed := catalogMisses imported modules solution
  unless missed.isEmpty do
    let byModule := modules.filterMap fun module =>
      let here := (missed.filter (·.1 == module)).map (·.2)
      if here.isEmpty then none else some (censusMessage (fileOf lake module) module here next)
    throw <| .userError ("\n".intercalate byModule.toList)

end SoftwareChallenge.Read

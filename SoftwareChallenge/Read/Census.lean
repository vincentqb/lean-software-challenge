module

public meta import Lean
public meta import SoftwareChallenge.CoreSpec.Facts
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

def closureUnlisted (lake : LakeFacts) (challenge : ChallengeFacts) : IO (Array Name) :=
  challenge.closure.filterM fun module => do
    if (packageModules lake).contains module then return false
    (oleanOf lake module).pathExists

def requireClosureCensus (lake : LakeFacts) (challenge : ChallengeFacts) (next : Next) : IO Unit := do
  let unlisted ← closureUnlisted lake challenge
  unless unlisted.isEmpty do
    throw <| .userError ("\n".intercalate (unlisted.map fun module =>
      s!"{sourcePath module}:1: {challenge.module} imports {module}, which the package builds, but lake.json does \
        not list it among the package's modules, so the step cannot tell which role it has or record it as owned; \
        no edit to the package fixes this. Make the facet in SoftwareChallenge's lakefile.lean list every module of \
        the challenge's import closure that the package builds, then run `{next.command}`.").toList)

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

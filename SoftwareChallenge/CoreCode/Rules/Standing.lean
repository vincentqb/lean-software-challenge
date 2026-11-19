module

public import SoftwareChallenge.CoreCode.Facts
public import SoftwareChallenge.CoreSpec.Lint

public section

namespace SoftwareChallenge

open Lean

instance Lint.decidableOwned (role : Role) : Decidable role.Owned :=
  inferInstanceAs (Decidable (role = .coreSpec ∨ role = .worldSpec))

instance Lint.decidableBuilds (lake : LakeFacts) (module : Name) : Decidable (lake.Builds module) :=
  inferInstanceAs (Decidable (∃ source ∈ lake.modules, source.module = module))

instance Lint.decidableOwns (challenge : ChallengeFacts) (module : Name) : Decidable (challenge.Owns module) :=
  inferInstanceAs (Decidable (module ∈ challenge.closure ∨ (Role.ofName module).Owned))

instance Lint.decidableProgram (lake : LakeFacts) : Decidable lake.Program :=
  inferInstanceAs (Decidable (∃ root ∈ lake.exeRoots, Role.ofName root = .worldCode))

instance Lint.decidableNamedSolution : DecidablePred Name.NamedSolution
  | .anonymous => isFalse id
  | .str _ last => inferInstanceAs (Decidable (last = "Solution"))
  | .num _ _ => isFalse id

instance Lint.decidableOneSolution (lake : LakeFacts) : Decidable lake.OneSolution :=
  inferInstanceAs (Decidable (∃ solution ∈ lake.modules, Name.NamedSolution solution.module ∧
    ∀ other ∈ lake.modules, Name.NamedSolution other.module → other.module = solution.module))

instance Lint.decidableDigested (files : FileFacts) (path : String) : Decidable (files.Digested path) :=
  inferInstanceAs (Decidable (∃ entry ∈ files.digests, entry.path = path))

instance Lint.decidableWithin (path directory : String) : Decidable (Path.Within path directory) :=
  inferInstanceAs (Decidable ((directory.splitOn "/").IsPrefix (path.splitOn "/")))

instance Lint.decidableVisible (package : PackageFact) (packageDir : String) : Decidable (package.Visible packageDir) :=
  inferInstanceAs (Decidable (Path.Within package.real packageDir ∨
    ∀ hidden ∈ sandboxHidden, ¬ Path.Within package.configured hidden ∧ ¬ Path.Within package.real hidden))

def SolutionFacts.present (solution : SolutionFacts) (constant : ConstantFact) : Bool :=
  solution.found.any (·.constant == constant)

def FoundFact.restates (found : FoundFact) (target : TargetFact) : Bool :=
  found.constant.kind == target.constant.kind && found.constant.levels == target.constant.levels &&
    found.constant.type == target.constant.type

def SolutionFacts.proves (solution : SolutionFacts) (target : TargetFact) (found : FoundFact) : Bool :=
  found.constant.name == target.constant.name && solution.solutionClosure.contains found.module &&
    found.restates target && target.auxiliaries.all solution.present

def SolutionFacts.holds (solution : SolutionFacts) (target : TargetFact) : Bool :=
  solution.found.any (solution.proves target)

def SolutionFacts.foundNamed? (solution : SolutionFacts) (name : Name) : Option FoundFact :=
  solution.found.find? (·.constant.name == name)

def SolutionFacts.unsound (solution : SolutionFacts) (name : Name) : Bool :=
  solution.inventory.declarations.any fun fact =>
    fact.name == name && fact.axioms.any (!standardAxioms.contains ·)

def standing (target : TargetFact) (found? : Option FoundFact) (inClosure importsSolution : Name → Bool)
    (present : ConstantFact → Bool) : Standing :=
  match found? with
  | none => .absent
  | some found =>
    if !inClosure found.module then .outside found.module (importsSolution found.module)
    else if found.constant.kind != target.constant.kind then .kind found.module found.constant.kind
    else if found.constant.levels != target.constant.levels then .universes found.module found.constant.levels
    else if found.constant.type != target.constant.type then
      .differs found.module found.rendered found.renderedExplicit
    else match target.auxiliaries.find? (!present ·) with
      | some auxiliary => .auxiliary found.module auxiliary.name
      | none => .holds found.module

def SolutionFacts.standingOf (solution : SolutionFacts) (target : TargetFact) : Standing :=
  match solution.found.find? (solution.proves target) with
  | some found => if solution.unsound target.constant.name then .unsound found.module else .holds found.module
  | none => standing target (solution.foundNamed? target.constant.name) solution.solutionClosure.contains
      solution.importsSolution.contains solution.present

def Standing.proved : Standing → Bool
  | .holds _ => true
  | _ => false

end SoftwareChallenge

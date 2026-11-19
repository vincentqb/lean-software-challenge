module

public import SoftwareChallenge.CoreSpec.Statement

@[expose] public section

namespace SoftwareChallenge

open Lean

inductive Standing where
  | holds (module : Name)
  | unsound (module : Name)
  | absent
  | outside (module : Name) (importsSolution : Bool)
  | kind (module : Name) (found : ConstantKind)
  | universes (module : Name) (found : List Name)
  | differs (module : Name) (plain explicit : String)
  | auxiliary (module : Name) (constant : Name)
  deriving BEq, Repr, Inhabited

namespace Lint

inductive Error where
  | unaudited (module : Name)
  | unlinted (module : Name)
  | metaImportsEditable (module : Name) (dependency : ImportFact)
  | violation (violation : Violation)
  | axiomUse (blame : AxiomBlame)
  | holeOutsideCode (hole module : Name)
  | holeNoncomputable (hole module : Name)
  | fixpointWithoutTerminates (hole module : Name)
  | declaredTwice (name first second : Name)
  | sorryUsed (place : Place)
  | mainOutsideProgram (module : Name)
  | notFixpoint (hole headline : Name)
  | claimOutsideWorldSpec (claim module : Name)
  | unregisteredClaim (registration : RegistrationFact)
  | lintWarning (lint : LintFact)
  | ownedUnread (path : String)
  | lock (violation : Lock.Violation) (owned? : Option OwnedFile)
  | lockMissing
  | lockUnreadable (problem : String)
  | comparatorMissing
  | comparatorStale (listedNotDeclared declaredNotListed : Array Name) (solutionListed? solutionExpected? : Option Name)
  | comparatorUnreadable (problem : String)
  | noStatementTarget
  | solutionModule (found : Array Name)
  | importsChallenge (importing : ImportLine)
  | builtinLintOn (place : Place)
  | proofUnreadable (target module : Name)
  deriving BEq, Repr, Inhabited

inductive Pending where
  | standing (target : Name) (standing : Standing)
  | mainMissing
  | unreachedHole (hole : Name)
  | undecidedCheck (use : ClaimUse) (check : CheckFact)
  | uncheckedClaim (use : ClaimUse)
  | hiddenDependency (dependency : PackageFact)
  deriving BEq, Repr, Inhabited

structure Result where
  errors : Array Error
  pending : Array Pending
  report : Array String
  code : UInt32
  deriving BEq, Repr, Inhabited

end Lint

def Config.Matches (config : Config) (challenge : ChallengeFacts) (solution : Name) : Prop :=
  config.challenge = challenge.module ∧ config.solution = solution ∧
    (∀ name, name ∈ config.theorems ↔ ∃ target ∈ challenge.theorems, target.constant.name = name) ∧
    (∀ name, name ∈ config.definitions ↔ ∃ hole ∈ challenge.holes, hole.constant.name = name) ∧
    ∀ name, name ∈ config.axioms ↔ name ∈ standardAxioms

def SolutionFacts.Holds (solution : SolutionFacts) (target : TargetFact) : Prop :=
  ∃ found ∈ solution.found, found.constant.name = target.constant.name ∧ found.module ∈ solution.solutionClosure ∧
    found.constant.kind = target.constant.kind ∧ found.constant.levels = target.constant.levels ∧
    found.constant.type = target.constant.type ∧
    ∀ auxiliary ∈ target.auxiliaries, ∃ same ∈ solution.found, same.constant = auxiliary

def SolutionFacts.Calls (solution : SolutionFacts) (caller callee : Name) : Prop :=
  ∃ entry ∈ solution.calls, entry.1 = caller ∧ callee ∈ entry.2

def Path.Within (path directory : String) : Prop :=
  (directory.splitOn "/").IsPrefix (path.splitOn "/")

def sandboxHidden : List String := ["/home", "/root", "/run", "/tmp", "/var"]

def PackageFact.Visible (package : PackageFact) (packageDir : String) : Prop :=
  Path.Within package.real packageDir ∨
    ∀ hidden ∈ sandboxHidden, ¬ Path.Within package.configured hidden ∧ ¬ Path.Within package.real hidden

structure Lint.Clean (facts : Facts) : Prop where
  modulesAudited : ∀ source ∈ facts.lake.modules, source.module ≠ facts.challenge.module →
    ∃ fact ∈ facts.solution.inventory.modules, fact.name = source.module
  exeRootsAudited : ∀ root ∈ facts.lake.exeRoots, ∃ fact ∈ facts.solution.inventory.modules, fact.name = root
  lintersCover : ∀ fact ∈ facts.solution.inventory.modules, fact.name ∈ facts.solution.linted
  lintersPass : facts.solution.lints = #[]
  noSorry : facts.solution.sorries = #[]
  admitted : facts.lake.project.Admits facts.solution.inventory
  specMetaImportsOwned : ∀ fact ∈ facts.solution.inventory.modules, (Role.ofName fact.name).Owned →
    ∀ dependency ∈ fact.imports, dependency.comptime = true → facts.lake.Builds dependency.name →
      facts.challenge.Owns dependency.name
  declaredOnce : ∀ fact ∈ facts.solution.inventory.declarations, ∀ other ∈ facts.solution.inventory.declarations,
    fact.name = other.name → fact.module = other.module
  holesInCode : ∀ hole ∈ facts.challenge.holes, ∀ found ∈ facts.solution.found,
    found.constant.name = hole.constant.name →
      facts.lake.project.role? found.module = some .coreCode ∨ facts.lake.project.role? found.module = some .worldCode
  holesCompiled : ∀ hole ∈ facts.challenge.holes, ∀ found ∈ facts.solution.found,
    found.constant.name = hole.constant.name → found.compiled = true
  mainInWorldCode : facts.lake.Program → ∀ main, facts.solution.main? = some main →
    facts.lake.project.role? main.1 = some .worldCode
  fixpointsDeclared : ∀ termination ∈ facts.challenge.terminating,
    (∃ found ∈ facts.solution.found, found.constant.name = termination.definition) →
      termination.definition ∈ facts.solution.fixpoints
  fixpointsTerminate : ∀ hole ∈ facts.challenge.holes, hole.constant.name ∈ facts.solution.fixpoints →
    ∃ termination ∈ facts.challenge.terminating, termination.definition = hole.constant.name
  claimsDeclared : ∀ registration ∈ facts.solution.registrations,
    registration.home? = some registration.module ∧ facts.lake.project.role? registration.module = some .worldSpec
  proofsReadable : ∀ headline ∈ facts.challenge.headlines, ∀ found ∈ facts.solution.found,
    found.constant.name = headline.target.constant.name → found.constant.kind = .proved →
      found.constant.value? ≠ none
  ownedDigested : ∀ path, facts.lake.Owned facts.challenge path → facts.files.Digested path
  lockCurrent : facts.files.LockCurrent
  comparatorCurrent : ∃ config, facts.files.comparator = .decoded config ∧
    ∃ solution ∈ facts.lake.modules, Name.NamedSolution solution.module ∧
      config.Matches facts.challenge solution.module
  oneSolution : facts.lake.OneSolution
  statementTarget : `statement ∈ facts.lake.defaultTargets
  challengeUnimported : ∀ line ∈ facts.solution.imports, line.fact.name ≠ facts.challenge.module
  builtinLintOff : facts.lake.builtinLint = none

structure Lint.Complete (facts : Facts) : Prop extends Lint.Clean facts where
  headlinesProved : ∀ headline ∈ facts.challenge.headlines, facts.solution.Holds headline.target
  holesDefined : ∀ hole ∈ facts.challenge.holes, facts.solution.Holds hole
  killsProved : ∀ kill ∈ facts.challenge.kills, facts.solution.Holds kill.target
  witnessesProved : ∀ witness ∈ facts.challenge.witnesses, facts.solution.Holds witness.target
  mainReachesHoles : facts.lake.Program → (∃ main, facts.solution.main? = some main) ∧
    ∀ hole ∈ facts.challenge.holes, Relation.TransGen facts.solution.Calls `main hole.constant.name
  claimsChecked : ∀ headline ∈ facts.challenge.headlines, ∀ index binder, headline.binders[index]? = some binder →
    binder.kind = .claim → ∃ use ∈ facts.solution.claimUses, use.headline = headline.target.constant.name ∧
      use.binder = index ∧ ∃ check ∈ use.checks, check.2 = .matched
  checksDecided : ∀ use ∈ facts.solution.claimUses, ∀ check ∈ use.checks, check.2 ≠ .undecided
  dependenciesVisible : ∀ package ∈ facts.lake.packages, package.Visible facts.lake.packageDir

end SoftwareChallenge

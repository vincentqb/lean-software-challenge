module

public import SoftwareChallenge.CoreSpec.Package
public import SoftwareChallenge.CoreSpec.Shape
public import SoftwareChallenge.CoreSpec.Telescope
public import SoftwareChallenge.CoreSpec.Format

@[expose] public section

namespace SoftwareChallenge

open Lean

structure Place where
  file : String
  line : Nat
  deriving BEq, Repr, Inhabited

structure SourceFact where
  module : Name
  file : String
  deriving BEq, Repr, Inhabited

structure PackageFact where
  name : Name
  configured : String
  real : String
  deriving BEq, Repr, Inhabited

inductive OwnTestKind where
  | script | library | executable
  deriving BEq, Repr, Inhabited

structure OwnTestFact where
  name : String
  kind : OwnTestKind
  place : Place
  deriving BEq, Repr, Inhabited

structure LakeFacts where
  packageDir : String
  repository? : Option String
  modules : Array SourceFact
  challengeCandidates : Array SourceFact
  exeRoots : Array Name
  packages : Array PackageFact
  defaultTargets : Array Name
  builtinLint : Option Place
  testDriver : String
  testDriverArgs : Array String
  testDriverArgsPlace : Place
  ownTests : Array OwnTestFact
  inputs : Array String
  deriving BEq, Repr, Inhabited

inductive Decoded (α : Type) where
  | missing
  | unreadable (problem : String)
  | decoded (value : α)
  deriving DecidableEq, Repr, Inhabited

structure FileFacts where
  lock : Decoded (Array Lock.Entry)
  comparator : Decoded Config
  digests : Array Lock.Entry
  deriving BEq, Repr, Inhabited

inductive Safety where
  | safe | «unsafe» | «partial»
  deriving DecidableEq, Repr, Inhabited

inductive ConstantKind where
  | assumed
  | defined (safety : Safety)
  | proved
  | opaqueConstant
  | quotient
  | inductiveType
  | constructor
  | recursor
  deriving DecidableEq, Repr, Inhabited

structure ConstantFact where
  name : Name
  kind : ConstantKind
  levels : List Name
  type : Shape
  value? : Option Shape
  hints : String
  mutualBlock : List Name
  isPrivate : Bool
  deriving DecidableEq, Repr, Inhabited

structure ImportLine where
  module : Name
  fact : ImportFact
  text : String
  deriving BEq, Repr, Inhabited

structure TargetFact where
  constant : ConstantFact
  place : Place
  written : String
  enclosingNamespace : Name
  signature : String
  rendered : String
  renderedExplicit : String
  auxiliaries : Array ConstantFact
  deriving BEq, Repr, Inhabited

structure HeadlineFact where
  target : TargetFact
  binders : List Binder
  claims : Array (Nat × Name × String)
  unnamed : Array String
  mentions : Array Name
  killTemplate? : Option String
  witness? : Option String
  deriving BEq, Repr, Inhabited

structure KillFact where
  target : TargetFact
  headline : Name
  deriving BEq, Repr, Inhabited

structure WitnessFact where
  target : TargetFact
  headline : Name
  derived : Bool
  deriving BEq, Repr, Inhabited

structure TerminationFact where
  definition : Name
  headline : Name
  place : Place
  deriving BEq, Repr, Inhabited

structure ChallengeFacts where
  module : Name
  file : String
  runtimeImports : Array ImportLine
  metaImports : Array ImportLine
  closure : Array Name
  headlines : Array HeadlineFact
  kills : Array KillFact
  witnesses : Array WitnessFact
  holes : Array TargetFact
  filled : Array (Name × Place)
  axioms : Array (Name × Place)
  terminating : Array TerminationFact
  replaceable : Array Name
  deriving BEq, Repr, Inhabited

structure FoundFact where
  constant : ConstantFact
  module : Name
  place : Place
  compiled : Bool
  rendered : String
  renderedExplicit : String
  deriving BEq, Repr, Inhabited

structure AxiomBlame where
  declaration : Name
  axiomName : Name
  culprit : Name
  culpritModule? : Option Name
  deriving BEq, Repr, Inhabited

structure CheckFact where
  claim : Name
  statement : String
  place : Place
  deriving BEq, Repr, Inhabited

inductive MatchOutcome where
  | matched | differs | undecided
  deriving DecidableEq, Repr, Inhabited

structure ClaimUse where
  headline : Name
  binder : Nat
  claim : Name
  statement : String
  checks : Array (CheckFact × MatchOutcome)
  deriving BEq, Repr, Inhabited

structure RegistrationFact where
  claim : Name
  module : Name
  home? : Option Name
  place : Place
  deriving BEq, Repr, Inhabited

structure LintFact where
  module : Name
  place : Place
  linter : Name
  message : String
  deriving BEq, Repr, Inhabited

structure DeclarationPlace where
  name : Name
  place : Place
  written : String
  firstLine : String
  deriving BEq, Repr, Inhabited

structure SolutionFacts where
  solution? : Option Name
  inventory : Inventory
  blames : Array AxiomBlame
  imports : Array ImportLine
  calls : Array (Name × Array Name)
  proofUses : Array (Name × Array Name)
  meanings : Array (Name × Array Name)
  found : Array FoundFact
  solutionClosure : Array Name
  importsSolution : Array Name
  premiseUses : Array (Name × Array Nat)
  claimUses : Array ClaimUse
  checks : Array CheckFact
  registrations : Array RegistrationFact
  lints : Array LintFact
  sorries : Array Place
  fixpoints : Array Name
  main? : Option (Name × Place)
  places : Array DeclarationPlace
  deriving BEq, Repr, Inhabited

structure CheckOutcome where
  check : CheckFact
  elapsed : Nat
  error? : Option String
  deriving BEq, Repr, Inhabited

inductive SampleOutcome where
  | held (headline : Name) (count : Nat)
  | counterexample (headline : Name) (inputs : String)
  | notSampled (headline : Name) (reason : String)
  deriving BEq, Repr, Inhabited

structure OwnTestRun where
  test : OwnTestFact
  code : UInt32
  deriving BEq, Repr, Inhabited

structure TestFacts where
  checks : Array CheckOutcome
  samples : Array SampleOutcome
  ownTests : Array OwnTestRun
  unknownOwnTests : Array String
  deriving BEq, Repr, Inhabited

structure Facts where
  lake : LakeFacts
  files : FileFacts
  challenge : ChallengeFacts
  solution : SolutionFacts
  deriving BEq, Repr, Inhabited

def Name.NamedSolution : Name → Prop
  | .str _ last => last = "Solution"
  | _ => False

def LakeFacts.OneSolution (lake : LakeFacts) : Prop :=
  ∃ solution ∈ lake.modules, Name.NamedSolution solution.module ∧
    ∀ other ∈ lake.modules, Name.NamedSolution other.module → other.module = solution.module

def LakeFacts.Builds (lake : LakeFacts) (module : Name) : Prop :=
  ∃ source ∈ lake.modules, source.module = module

def LakeFacts.project (lake : LakeFacts) : Project :=
  { modules := lake.modules.map fun source => (source.module, Role.ofName source.module) }

def FileFacts.LockCurrent (files : FileFacts) : Prop :=
  ∃ locked, files.lock = .decoded locked ∧ ∀ path, Lock.digestOf locked path = Lock.digestOf files.digests path

def ChallengeFacts.theorems (challenge : ChallengeFacts) : Array TargetFact :=
  challenge.headlines.map (·.target) ++ challenge.kills.map (·.target) ++ challenge.witnesses.map (·.target)

def ChallengeFacts.targets (challenge : ChallengeFacts) : Array TargetFact :=
  challenge.theorems ++ challenge.holes

end SoftwareChallenge

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
  overridden : Bool := false
  deriving BEq, Repr

inductive OwnTestKind where
  | script | library | executable
  deriving BEq, Repr, Inhabited

structure OwnTestFact where
  name : String
  kind : OwnTestKind
  place : Place
  deriving BEq, Repr, Inhabited

def auditLintDriver : String := "software_challenge/lint_challenge"

def auditTestDriver : String := "software_challenge/test_challenge"

structure LakeFacts where
  packageDir : String
  configFiles : Array String
  modules : Array SourceFact
  challengeCandidates : Array SourceFact
  defaultExeRoots : Array Name
  packages : Array PackageFact
  defaultTargets : Array Name
  builtinLint : Option Place
  lintDriver : String := auditLintDriver
  testDriver : String := auditTestDriver
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
  deriving Repr, Inhabited

inductive Safety where
  | safe | «unsafe» | «partial»
  deriving DecidableEq, Repr

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
  deriving Repr, Inhabited

structure BinderFact where
  name : String
  type : Shape
  meaning : Shape
  expanded : Shape := meaning
  prop : Bool
  shown : String
  conclusion : String
  variables : Array String
  level : Universe := .zero
  deriving BEq, Repr, Inhabited

structure HeadlineFact where
  target : TargetFact
  telescope : List BinderFact
  killTemplate? : Option String
  witness? : Option String
  deriving Repr, Inhabited

structure KillFact where
  target : TargetFact
  headline : Name
  deriving Repr, Inhabited

structure WitnessFact where
  target : TargetFact
  headline : Name
  derived : Bool
  deriving Repr, Inhabited

structure TerminationFact where
  definition : Name
  headline : Name
  place : Place
  deriving Repr, Inhabited

structure AxiomBlame where
  declaration : Name
  axiomName : Name
  culprit : Name
  culpritModule? : Option Name
  deriving BEq, Repr

structure RegistrationFact where
  claim : Name
  module : Name
  home? : Option Name
  place : Place
  deriving BEq, Repr

structure DeclarationPlace where
  name : Name
  place : Place
  written : String
  firstLine : String
  deriving Repr

structure OwnedFacts where
  inventory : Inventory := ⟨#[], #[]⟩
  imports : Array ImportLine := #[]
  blames : Array AxiomBlame := #[]
  registrations : Array RegistrationFact := #[]
  places : Array DeclarationPlace := #[]
  parents : Array (Name × Name) := #[]
  deriving Repr

structure ChallengeFacts where
  module : Name
  file : String
  runtimeImports : Array ImportLine
  metaImports : Array ImportLine
  closure : Array Name
  imports : Array (Name × Array Name) := #[]
  headlines : Array HeadlineFact
  kills : Array KillFact
  witnesses : Array WitnessFact
  holes : Array TargetFact
  filled : Array (Name × Place)
  axioms : Array (Name × Place)
  terminating : Array TerminationFact
  replaceable : Array Name
  claims : Array Name := #[]
  owned : OwnedFacts := {}
  deriving Repr, Inhabited

structure FoundFact where
  constant : ConstantFact
  module : Name
  place : Place
  compiled : Bool
  rendered : String
  renderedExplicit : String
  deriving Repr

structure CheckFact where
  claim : Name
  statement : String
  place : Place
  deriving Repr, Inhabited

inductive MatchOutcome where
  | matched | differs | undecided
  deriving DecidableEq, Repr

structure ClaimUse where
  headline : Name
  binder : Nat
  claim : Name
  statement : String
  checks : Array (CheckFact × MatchOutcome)
  deriving Repr

structure LintFact where
  module : Name
  place : Place
  linter : Name
  message : String
  deriving BEq, Repr

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
  linted : Array Name
  sorries : Array Place
  fixpoints : Array Name
  main? : Option (Name × Place)
  places : Array DeclarationPlace
  parents : Array (Name × Name) := #[]
  deriving Repr, Inhabited

structure CheckOutcome where
  check : CheckFact
  elapsed : Nat
  error? : Option String
  deriving Inhabited

structure OwnTestRun where
  test : OwnTestFact
  code : UInt32
  deriving Inhabited

structure TestFacts where
  declaredChecks : Array CheckFact
  checks : Array CheckOutcome
  declaredOwnTests : Array OwnTestFact
  ownTests : Array OwnTestRun
  unknownOwnTests : Array String
  testDriverArgsPlace : Place
  libraryPlace : Place
  deriving Inhabited

structure Facts where
  lake : LakeFacts
  files : FileFacts
  challenge : ChallengeFacts
  solution : SolutionFacts
  deriving Repr, Inhabited

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

def LakeFacts.Program (lake : LakeFacts) : Prop :=
  ∃ root ∈ lake.defaultExeRoots, Role.ofName root = .worldCode

def ChallengeFacts.Owns (challenge : ChallengeFacts) (module : Name) : Prop :=
  module ∈ challenge.closure ∨ (Role.ofName module).Owned

def ChallengeFacts.owns (challenge : ChallengeFacts) (module : Name) : Bool :=
  challenge.closure.contains module || Role.ofName module == .coreSpec || Role.ofName module == .worldSpec

def Inventory.restrictedTo (inventory : Inventory) (keep : Name → Bool) : Inventory :=
  { modules := inventory.modules.filter (keep ·.name), declarations := inventory.declarations.filter (keep ·.module) }

def Telescope.Depended (telescope : List BinderFact) (index : Nat) : Prop :=
  ∃ later binder, telescope[later]? = some binder ∧ index < later ∧ binder.type.Refers (later - 1 - index)

def HeadlineFact.Claim (claims : Array Name) (headline : HeadlineFact) (index : Nat) : Prop :=
  ∃ binder, headline.telescope[index]? = some binder ∧ binder.prop = true ∧
    ¬ Telescope.Depended headline.telescope index ∧ ∃ claim ∈ claims, binder.meaning.Concludes claim

def HeadlineFact.Precondition (claims : Array Name) (headline : HeadlineFact) (index : Nat) : Prop :=
  ∃ binder, headline.telescope[index]? = some binder ∧ binder.prop = true ∧
    ¬ Telescope.Depended headline.telescope index ∧ ¬ ∃ claim ∈ claims, binder.meaning.Concludes claim

def HeadlineFact.Mentions (replaceable : Name → Bool) (headline : HeadlineFact) (index : Nat) : Prop :=
  ∃ binder, headline.telescope[index]? = some binder ∧ ∃ name, replaceable name = true ∧ binder.meaning.Mentions name

def BinderFact.Open (binder : BinderFact) (index : Nat) : Prop :=
  ∃ earlier < index, binder.type.Refers earlier

def ChallengeFacts.Foreign (challenge : ChallengeFacts) (name : Name) : Prop :=
  name ∈ challenge.replaceable ∧ ∀ hole ∈ challenge.holes, hole.constant.name ≠ name

def HeadlineFact.ClaimConstrains (claims : Array Name) (headline : HeadlineFact) (index : Nat) (binder : BinderFact)
    (name : Name) : Prop :=
  headline.telescope[index]? = some binder ∧ headline.Claim claims index ∧ binder.expanded.Mentions name

def LakeFacts.Owned (lake : LakeFacts) (challenge : ChallengeFacts) (path : String) : Prop :=
  path ∈ lake.configFiles ∨ path = challenge.file ∨
    ∃ source ∈ lake.modules, challenge.Owns source.module ∧ source.file = path

def FileFacts.Digested (files : FileFacts) (path : String) : Prop :=
  ∃ entry ∈ files.digests, entry.path = path

def FileFacts.LockCurrent (files : FileFacts) : Prop :=
  ∃ locked, files.lock = .decoded locked ∧ ∀ path, Lock.digestOf locked path = Lock.digestOf files.digests path

def ChallengeFacts.theorems (challenge : ChallengeFacts) : Array TargetFact :=
  challenge.headlines.map (·.target) ++ challenge.kills.map (·.target) ++ challenge.witnesses.map (·.target)

def ChallengeFacts.targets (challenge : ChallengeFacts) : Array TargetFact :=
  challenge.theorems ++ challenge.holes

end SoftwareChallenge

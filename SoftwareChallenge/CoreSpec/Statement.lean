module

public import SoftwareChallenge.CoreSpec.Facts

@[expose] public section

namespace SoftwareChallenge

open Lean

inductive OwnedFile where
  | lakefile | manifest | toolchain | challenge
  | specModule (module : Name)
  | closureModule (module : Name)
  deriving BEq, Repr, Inhabited

namespace Statement

inductive Error where
  | duplicate (later earlier : Name)
  | mentionsNothing (headline : Name)
  | noKill (headline : Name) (suggestion? : Option String)
  | unmarkedKill (headline kill : Name)
  | killOfNonHeadline (kill named : Name)
  | killReplacesNothing (kill headline : Name)
  | misshapenKill (kill headline : Name)
  | unmentionedHole (hole : Name)
  | challengeImport (dependency : ImportLine) (role? : Option Role)
  | filled (name : Name)
  | challengeAxiom (name : Name)
  | privateTarget (name : Name)
  | terminatesNotHole (headline definition : Name)
  | terminatesWithoutKill (headline definition : Name)
  | terminatesUnmentioned (headline definition : Name)
  | unnamedHypothesis (headline : Name) (hypothesis : String)
  | privateAuxiliary (headline auxiliary : Name)
  | codeInClosure (module : Name)
  | witnessMissing (headline : Name)
  | witnessPredeclared (witness headline : Name)
  | unplainName (name : Name)
  | challengeLookup (candidates : Array SourceFact)
  | challengeAbsent (module : Name) (file : String)
  | challengeFails (file : String)
  | solutionModule (found : Array Name)
  | importsChallenge (importing : ImportLine)
  | noStatementTarget
  | exeRootsOutsideWorldCode (roots : Array Name)
  | ownedUnread (path : String)
  | lock (violation : Lock.Violation) (owned? : Option OwnedFile)
  | lockUnreadable (problem : String)
  deriving BEq, Repr, Inhabited

structure Writes where
  lock? : Option (Array Lock.Entry)
  config? : Option Config
  deriving BEq, Repr, Inhabited

structure Result where
  errors : Array Error
  writes : Writes
  killSearch : Array Name
  code : UInt32
  deriving BEq, Repr, Inhabited

end Statement

def ChallengeFacts.isReplaceable (challenge : ChallengeFacts) (name : Name) : Bool :=
  challenge.replaceable.contains name

def ChallengeFacts.othersOf (challenge : ChallengeFacts) (headline : HeadlineFact) : List Shape :=
  (challenge.headlines.toList.filter (·.target.constant.name != headline.target.constant.name)).map
    (·.target.constant.type)

structure Statement.Complete (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Prop where
  challengeFound : ∃ candidate, lake.challengeCandidates = #[candidate] ∧ candidate.module = challenge.module
  oneSolution : lake.OneSolution
  statementTarget : `statement ∈ lake.defaultTargets
  programRooted : lake.exeRoots ≠ #[] → (∃ source ∈ lake.modules, Role.ofName source.module = .worldCode) →
    lake.Program
  importsOnlySpecs : ∀ line ∈ challenge.runtimeImports, lake.Builds line.fact.name →
    Role.ofName line.fact.name = .coreSpec ∨ Role.ofName line.fact.name = .worldSpec
  closureHoldsNoCode : ∀ module ∈ challenge.closure, lake.Builds module →
    Role.ofName module ≠ .coreCode ∧ Role.ofName module ≠ .worldCode
  declaresOnlyTheoremsAndHoles : challenge.filled = #[]
  assumesNoAxiom : challenge.axioms = #[]
  targetsPublic : ∀ target ∈ challenge.targets, target.constant.isPrivate = false
  namesPlain : ∀ target ∈ challenge.targets, Name.Plain target.constant.name
  auxiliariesPublic : ∀ target ∈ challenge.targets, ∀ auxiliary ∈ target.auxiliaries, auxiliary.isPrivate = false
  headlinesMentionHoles : ∀ headline ∈ challenge.headlines,
    ∃ name, challenge.isReplaceable name = true ∧ headline.target.constant.type.Mentions name
  headlinesKilled : ∀ headline ∈ challenge.headlines,
    ∃ kill ∈ challenge.kills, kill.headline = headline.target.constant.name
  killsNameHeadlines : ∀ kill ∈ challenge.kills,
    ∃ headline ∈ challenge.headlines, headline.target.constant.name = kill.headline
  killsReject : ∀ kill ∈ challenge.kills, ∀ headline ∈ challenge.headlines,
    kill.headline = headline.target.constant.name →
      headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
        kill.target.constant.type
  killsMarked : ∀ headline ∈ challenge.headlines, ∀ other ∈ challenge.headlines,
    ¬ headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
      other.target.constant.type
  headlinesDistinct : (challenge.headlines.toList.map (·.target.constant.type)).Nodup
  holesMentioned : ∀ hole ∈ challenge.holes,
    ∃ headline ∈ challenge.headlines, headline.target.constant.type.Mentions hole.constant.name
  hypothesesClaimed : ∀ headline ∈ challenge.headlines, ∀ binder ∈ headline.binders,
    binder.kind = .precondition → binder.refers ≠ []
  preconditionsWitnessed : ∀ headline ∈ challenge.headlines,
    (∃ binder ∈ headline.binders, binder.kind ≠ .claim ∧ binder.mentions = true) →
      ∃ witness ∈ challenge.witnesses, witness.headline = headline.target.constant.name
  witnessesDerived : ∀ witness ∈ challenge.witnesses, witness.derived = true
  terminatesNamesHole : ∀ termination ∈ challenge.terminating,
    ∃ hole ∈ challenge.holes, hole.constant.name = termination.definition
  terminatesOnKilledHeadline : ∀ termination ∈ challenge.terminating,
    (∃ headline ∈ challenge.headlines, headline.target.constant.name = termination.headline) ∧
      ∃ kill ∈ challenge.kills, kill.headline = termination.headline
  terminatesMentionsHole : ∀ termination ∈ challenge.terminating, ∀ headline ∈ challenge.headlines,
    headline.target.constant.name = termination.headline → headline.target.constant.type.Mentions termination.definition
  ownedDigested : ∀ path, lake.Owned challenge path → files.Digested path
  lockCurrent : files.lock = .missing ∨ files.LockCurrent

end SoftwareChallenge

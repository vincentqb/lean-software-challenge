module

public import SoftwareChallenge.CoreCode.Facts
public import SoftwareChallenge.CoreSpec.Statement
public import SoftwareChallenge.CoreCode.Classify
public import SoftwareChallenge.CoreCode.Layering
public import SoftwareChallenge.CoreCode.Match
public import SoftwareChallenge.CoreCode.Format

public section

namespace SoftwareChallenge.Statement

open Lean

def builds (lake : LakeFacts) (module : Name) : Bool :=
  lake.modules.any (·.module == module)

def namedSolution : Name → Bool
  | .str _ last => last == "Solution"
  | _ => false

def solutions (lake : LakeFacts) : Array Name :=
  (lake.modules.filter (namedSolution ·.module)).map (·.module)

def solution? (lake : LakeFacts) : Option Name :=
  match (solutions lake).toList with
  | first :: rest => if rest.all (· == first) then some first else none
  | [] => none

def plainCharacter (char : Char) : Bool :=
  char != '.' && char != '"' && char != '\\' && char != '«' && char != '»' && decide (' ' ≤ char)

def plainComponent (component : String) : Bool :=
  match component.toList with
  | [] => false
  | first :: rest => !first.isDigit && (first :: rest).all plainCharacter

def plain : Name → Bool
  | .anonymous => false
  | .str parent component => (parent == .anonymous || plain parent) && plainComponent component
  | .num _ _ => false

def negated? : Shape → Option Shape
  | .app (.const name []) statement => if name = ``Not then some statement else none
  | _ => none

def conjunct? : Shape → Option (Shape × Shape)
  | .app (.app (.const name []) first) rest => if name = ``And then some (first, rest) else none
  | _ => none

def conjuncts : Nat → Shape → Option (List Shape)
  | 0, statement => some [statement]
  | count + 1, statement => match conjunct? statement with
    | some (first, rest) => (conjuncts count rest).map (first :: ·)
    | none => none

def tuple : List Shape → Shape
  | [] => .bvar 0
  | statement :: rest => .app (tuple rest) statement

def plainKill (replaceable : Name → Bool) (headline kill : Shape) : Bool :=
  match negated? kill with
  | some rejected => rejected != headline && (headline.witnesses? replaceable rejected).isSome
  | none => false

def independenceKill (replaceable : Name → Bool) (headline : Shape) (others : List Shape) (kill : Shape) : Bool :=
  !others.isEmpty && match conjuncts others.length kill with
    | some (first :: rest) => match negated? first with
      | some rejected => rejected != headline &&
        ((tuple (headline :: others)).witnesses? replaceable (tuple (rejected :: rest))).isSome
      | none => false
    | _ => false

def killedBy (replaceable : Name → Bool) (headline : Shape) (others : List Shape) (kill : Shape) : Bool :=
  plainKill replaceable headline kill || independenceKill replaceable headline others kill

def replacesNothing (headline : Shape) (others : List Shape) (kill : Shape) : Bool :=
  kill == headline.negation || !others.isEmpty && kill == Shape.conjunction (headline.negation :: others)

def duplicatesFrom (seen : List (Name × Shape)) : List (Name × Shape) → List (Name × Name)
  | [] => []
  | (name, statement) :: rest =>
    let later := duplicatesFrom (seen ++ [(name, statement)]) rest
    match seen.find? (·.2 == statement) with
    | some earlier => (name, earlier.1) :: later
    | none => later

def duplicates (challenge : ChallengeFacts) : List (Name × Name) :=
  duplicatesFrom [] (challenge.headlines.toList.map fun headline =>
    (headline.target.constant.name, headline.target.constant.type))

def laterDuplicate (challenge : ChallengeFacts) (headline : HeadlineFact) : Bool :=
  (duplicates challenge).any (·.1 == headline.target.constant.name)

def unreproducible (headline : HeadlineFact) : Bool :=
  headline.target.auxiliaries.any (·.isPrivate)

def mentionsReplaceable (challenge : ChallengeFacts) (headline : HeadlineFact) : Bool :=
  headline.target.constant.type.constants.any challenge.isReplaceable

def killsHeadline (challenge : ChallengeFacts) (headline : HeadlineFact) (kill : Shape) : Bool :=
  killedBy challenge.isReplaceable headline.target.constant.type (challenge.othersOf headline) kill

def killsAnother (challenge : ChallengeFacts) (headline : HeadlineFact) : Bool :=
  challenge.headlines.any fun other => killsHeadline challenge other headline.target.constant.type

def hasKill (challenge : ChallengeFacts) (headline : Name) : Bool :=
  challenge.kills.any (·.headline == headline)

def settled (challenge : ChallengeFacts) (headline : HeadlineFact) : Bool :=
  laterDuplicate challenge headline || unreproducible headline || !mentionsReplaceable challenge headline

def unmarked (challenge : ChallengeFacts) (headline : HeadlineFact) : Bool :=
  challenge.headlines.any (fun other => killsHeadline challenge headline other.target.constant.type) ||
    killsAnother challenge headline

def needsWitness (challenge : ChallengeFacts) (headline : HeadlineFact) : Bool :=
  (headline.binders challenge).any fun binder => binder.kind != .claim && binder.mentions

def closedHypothesis (challenge : ChallengeFacts) (headline : HeadlineFact) (index : Nat) (binder : BinderFact) :
    Bool :=
  Telescope.kindAt challenge.isClaim headline.telescope index binder == .precondition &&
    (Telescope.refersAt index binder).isEmpty

def closedHypotheses (challenge : ChallengeFacts) (headline : HeadlineFact) : List BinderFact :=
  (headline.telescope.zipIdx.filter fun (binder, index) => closedHypothesis challenge headline index binder).map (·.1)

def ownsModule (challenge : ChallengeFacts) (module : Name) : Bool :=
  challenge.owns module

def ownedPaths (lake : LakeFacts) (challenge : ChallengeFacts) : Array String :=
  lake.configFiles ++ #[challenge.file] ++ (lake.modules.filter (ownsModule challenge ·.module)).map (·.file)

def digested (files : FileFacts) (path : String) : Bool :=
  files.digests.any (·.path == path)

def recorded (files : FileFacts) (path : String) : Bool :=
  match files.lock with
  | .decoded locked => locked.any (·.path == path)
  | _ => false

def ownedFile? (lake : LakeFacts) (challenge : ChallengeFacts) (path : String) : Option OwnedFile :=
  if path = challenge.file then some .challenge
  else if path = "lake-manifest.json" then some .manifest
  else if path = "lean-toolchain" then some .toolchain
  else if path = "lakefile.lean" ∨ path = "lakefile.toml" ∨ lake.configFiles.contains path then some .lakefile
  else match lake.modules.find? (·.file == path) with
    | some source =>
      if Role.ofName source.module == .coreSpec || Role.ofName source.module == .worldSpec then
        some (.specModule source.module)
      else if challenge.closure.contains source.module then some (.closureModule source.module)
      else none
    | none => none

def violationPath : Lock.Violation → String
  | .unrecorded path | .differs path | .missing path => path

def challengeErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  match lake.challengeCandidates.toList with
  | [candidate] =>
    if candidate.module = challenge.module then #[] else #[.challengeAbsent candidate.module candidate.file]
  | _ => #[.challengeLookup lake.challengeCandidates]

def solutionErrors (lake : LakeFacts) : Array Error :=
  if (solution? lake).isSome then #[] else #[.solutionModule (solutions lake)]

def targetErrors (lake : LakeFacts) : Array Error :=
  if lake.defaultTargets.contains `statement then #[] else #[.noStatementTarget]

def programErrors (lake : LakeFacts) : Array Error :=
  if lake.defaultExeRoots.isEmpty || !lake.modules.any (Role.ofName ·.module == .worldCode) ||
      lake.defaultExeRoots.any (Role.ofName · == .worldCode) then #[]
  else #[.exeRootsOutsideWorldCode lake.defaultExeRoots]

def specRole (module : Name) : Bool :=
  Role.ofName module == .coreSpec || Role.ofName module == .worldSpec

def ownedRoots (lake : LakeFacts) (challenge : ChallengeFacts) : Array Name :=
  (lake.modules.filter fun source => source.module != challenge.module && ownsModule challenge source.module).map
    (·.module)

def codeRole (module : Name) : Bool :=
  Role.ofName module == .coreCode || Role.ofName module == .worldCode

def ownedInventory (challenge : ChallengeFacts) : Inventory :=
  challenge.owned.inventory.restrictedTo challenge.owns

def ownedViolationErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  (lake.project.violations (ownedInventory challenge)).map .ownedViolation

def specImportErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  challenge.owned.inventory.modules.flatMap fun fact =>
    if specRole fact.name then
      fact.imports.filterMap fun dependency =>
        if dependency.comptime && builds lake dependency.name && !ownsModule challenge dependency.name then
          some (.specImport fact.name dependency)
        else none
    else #[]

def claimDeclared (lake : LakeFacts) (registration : RegistrationFact) : Bool :=
  registration.home? == some registration.module && lake.project.role? registration.module == some .worldSpec

def ownedClaimErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  challenge.owned.registrations.filterMap fun registration =>
    if ownsModule challenge registration.module && !claimDeclared lake registration then some (.ownedClaim registration)
    else none

def derivedPartialErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.owned.inventory.declarations.filterMap fun fact =>
    if fact.derivedPartial && ownsModule challenge fact.module then some (.derivedPartial fact.name fact.module)
    else none

def ownerErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  ownedViolationErrors lake challenge ++ specImportErrors lake challenge ++ ownedClaimErrors lake challenge ++
    derivedPartialErrors challenge

def importErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  challenge.runtimeImports.filterMap fun line =>
    if builds lake line.fact.name && !specRole line.fact.name then
      some (.challengeImport line (some (Role.ofName line.fact.name)))
    else none

def closureErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  challenge.closure.filterMap fun module =>
    if builds lake module && codeRole module && !challenge.runtimeImports.any (·.fact.name == module) then
      some (.codeInClosure module)
    else none

def filledErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.filled.map (.filled ·.1)

def axiomErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.axioms.map (.challengeAxiom ·.1)

def privateErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.targets.filterMap fun target =>
    if target.constant.isPrivate then some (.privateTarget target.constant.name) else none

def plainErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.targets.filterMap fun target =>
    if target.constant.isPrivate || plain target.constant.name then none else some (.unplainName target.constant.name)

def auxiliaryErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.targets.flatMap fun target =>
    (target.auxiliaries.filter (·.isPrivate)).map (.privateAuxiliary target.constant.name ·.name)

def duplicateErrors (challenge : ChallengeFacts) : Array Error :=
  ((duplicates challenge).map fun (later, earlier) => Error.duplicate later earlier).toArray

def mentionErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.headlines.filterMap fun headline =>
    if mentionsReplaceable challenge headline || laterDuplicate challenge headline || unreproducible headline ||
        killsAnother challenge headline then none
    else some (.mentionsNothing headline.target.constant.name)

def unmarkedErrors (challenge : ChallengeFacts) : Array Error :=
  (challenge.headlines.filter (!laterDuplicate challenge ·)).flatMap fun headline =>
    (challenge.headlines.filter fun kill =>
      !laterDuplicate challenge kill && killsHeadline challenge headline kill.target.constant.type).map
        (.unmarkedKill headline.target.constant.name ·.target.constant.name)

def noKillErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.headlines.filterMap fun headline =>
    if hasKill challenge headline.target.constant.name || settled challenge headline || unmarked challenge headline then
      none
    else some (.noKill headline.target.constant.name headline.killTemplate?)

def killErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.kills.flatMap fun kill =>
    let named := challenge.headlines.filter (·.target.constant.name == kill.headline)
    if named.isEmpty then #[.killOfNonHeadline kill.target.constant.name kill.headline]
    else named.filterMap fun headline =>
      if settled challenge headline || killsHeadline challenge headline kill.target.constant.type then none
      else if replacesNothing headline.target.constant.type (challenge.othersOf headline) kill.target.constant.type then
        some (.killReplacesNothing kill.target.constant.name headline.target.constant.name)
      else some (.misshapenKill kill.target.constant.name headline.target.constant.name)

def holeErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.holes.filterMap fun hole =>
    if challenge.headlines.any (fun headline => headline.target.constant.type.constants.contains hole.constant.name)
    then none
    else some (.unmentionedHole hole.constant.name)

def hypothesisErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.headlines.flatMap fun headline =>
    ((closedHypotheses challenge headline).map (Error.unnamedHypothesis headline.target.constant.name)).toArray

def misstated (challenge : ChallengeFacts) (witness : WitnessFact) : Bool :=
  challenge.headlines.any fun headline =>
    headline.target.constant.name == witness.headline &&
      witness.target.constant.type != headline.expectedWitness challenge

def witnessErrors (challenge : ChallengeFacts) : Array Error :=
  (challenge.headlines.filterMap fun headline =>
    if needsWitness challenge headline && hasKill challenge headline.target.constant.name &&
        !challenge.witnesses.any (·.headline == headline.target.constant.name) then
      some (.witnessMissing headline.target.constant.name)
    else none) ++
  (challenge.witnesses.filterMap fun witness =>
    if witness.derived then none else some (.witnessPredeclared witness.target.constant.name witness.headline)) ++
  challenge.witnesses.filterMap fun witness =>
    if misstated challenge witness then some (.witnessMisstated witness.target.constant.name witness.headline)
    else none

def terminationErrors (challenge : ChallengeFacts) : Array Error :=
  challenge.terminating.flatMap fun termination =>
    (if challenge.holes.any (·.constant.name == termination.definition) then #[]
      else #[.terminatesNotHole termination.headline termination.definition]) ++
    (if challenge.headlines.any (·.target.constant.name == termination.headline) &&
        hasKill challenge termination.headline then #[]
      else #[.terminatesWithoutKill termination.headline termination.definition]) ++
    (if challenge.headlines.all fun headline => headline.target.constant.name != termination.headline ||
        headline.target.constant.type.constants.contains termination.definition then #[]
      else #[.terminatesUnmentioned termination.headline termination.definition])

def unreadErrors (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Array Error :=
  (ownedPaths lake challenge).filterMap fun path =>
    if digested files path || recorded files path then none else some (.ownedUnread path)

def lockErrors (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Array Error :=
  match files.lock with
  | .missing => #[]
  | .unreadable problem => #[.lockUnreadable problem]
  | .decoded locked =>
    (Lock.violations locked files.digests).map fun violation =>
      .lock violation (ownedFile? lake challenge (violationPath violation))

def setupErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  challengeErrors lake challenge ++ solutionErrors lake ++ targetErrors lake ++ programErrors lake

def ownershipErrors (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  importErrors lake challenge ++ closureErrors lake challenge ++ filledErrors challenge ++ axiomErrors challenge ++
    privateErrors challenge ++ plainErrors challenge ++ ownerErrors lake challenge

def meaningErrors (challenge : ChallengeFacts) : Array Error :=
  duplicateErrors challenge ++ mentionErrors challenge ++ unmarkedErrors challenge ++ noKillErrors challenge ++
    killErrors challenge ++ witnessErrors challenge ++ holeErrors challenge

def statedErrors (challenge : ChallengeFacts) : Array Error :=
  terminationErrors challenge ++ hypothesisErrors challenge ++ auxiliaryErrors challenge

def findings (lake : LakeFacts) (challenge : ChallengeFacts) : Array Error :=
  setupErrors lake challenge ++ ownershipErrors lake challenge ++ meaningErrors challenge ++ statedErrors challenge

def lockingErrors (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Array Error :=
  unreadErrors lake files challenge ++ lockErrors lake files challenge

def errors (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Array Error :=
  let lookup := challengeErrors lake challenge
  let locking := lockingErrors lake files challenge
  if !lookup.isEmpty then lookup ++ solutionErrors lake
  else if !locking.isEmpty then locking ++ solutionErrors lake
  else findings lake challenge

def writesOf (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Writes :=
  { lock? := match files.lock with
      | .missing => some files.digests
      | _ => none
    config? := (solution? lake).map (Config.expected challenge) }

def lintDriverSetup (lake : LakeFacts) : Array Setup :=
  if lake.lintDriver = auditLintDriver then #[] else #[.lintDriver lake.lintDriver]

def testDriverSetup (lake : LakeFacts) : Array Setup :=
  if lake.testDriver = auditTestDriver then #[] else #[.testDriver lake.testDriver]

def builtinLintSetup (lake : LakeFacts) : Array Setup :=
  match lake.builtinLint with
  | some place => #[.builtinLint place]
  | none => #[]

def setupOf (lake : LakeFacts) : Array Setup :=
  lintDriverSetup lake ++ testDriverSetup lake ++ builtinLintSetup lake

def run (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Result :=
  let setup := setupOf lake
  let found := errors lake files challenge
  let clean := setup.isEmpty && found.isEmpty
  { setup, errors := found
    writes := if clean then writesOf lake files challenge else { lock? := none, config? := none }
    code := if clean then 0 else 1 }

theorem plainCharacter_eq_true {char : Char} : plainCharacter char = true ↔ Name.PlainCharacter char := by
  simp [plainCharacter, Name.PlainCharacter, and_assoc]

theorem plainComponent_eq_true {component : String} :
    plainComponent component = true ↔ Name.PlainComponent component := by
  unfold plainComponent Name.PlainComponent
  cases component.toList with
  | nil => simp
  | cons first rest => simp [List.all_eq_true, plainCharacter_eq_true]

theorem plain_eq_true {name : Name} : plain name = true ↔ Name.Plain name := by
  induction name with
  | anonymous => simp [plain, Name.Plain]
  | str parent component ih =>
    simp [plain, Name.Plain, ih, plainComponent_eq_true]
  | num => simp [plain, Name.Plain]

theorem negated?_eq_some {shape statement : Shape} : negated? shape = some statement ↔ shape = statement.negation := by
  unfold negated?
  split
  · rename_i name inner
    by_cases named : name = ``Not
    · subst named
      simp [Shape.negation]
    · simp [named, Shape.negation]
  · rename_i different
    simp only [reduceCtorEq, false_iff]
    rintro rfl
    exact different _ _ rfl

theorem conjunct?_eq_some {shape first rest : Shape} :
    conjunct? shape = some (first, rest) ↔ shape = .app (.app (.const ``And []) first) rest := by
  unfold conjunct?
  split
  · rename_i name left right
    by_cases named : name = ``And
    · subst named
      simp
    · simp [named]
  · rename_i different
    simp only [reduceCtorEq, false_iff]
    rintro rfl
    exact different _ _ _ rfl

theorem conjuncts_eq_some {count : Nat} {shape : Shape} {parts : List Shape} :
    conjuncts count shape = some parts ↔ parts.length = count + 1 ∧ Shape.conjunction parts = shape := by
  induction count generalizing shape parts with
  | zero =>
    simp only [conjuncts, Option.some.injEq, Nat.zero_add]
    constructor
    · rintro rfl
      simp [Shape.conjunction]
    · rintro ⟨length, joined⟩
      cases parts with
      | nil => simp at length
      | cons single rest =>
        cases rest with
        | nil => simp_all [Shape.conjunction]
        | cons => simp at length
  | succ count ih =>
    simp only [conjuncts]
    cases split : conjunct? shape with
    | none =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro length joined
      cases parts with
      | nil => simp at length
      | cons first tail =>
        cases tail with
        | nil => simp at length
        | cons next more =>
          have unfolded : Shape.conjunction (first :: next :: more) =
              .app (.app (.const ``And []) first) (Shape.conjunction (next :: more)) := by
            simp [Shape.conjunction]
          have conjoined : conjunct? (.app (.app (.const ``And []) first) (Shape.conjunction (next :: more))) =
              some (first, Shape.conjunction (next :: more)) := conjunct?_eq_some.mpr rfl
          rw [← joined, unfolded, conjoined] at split
          cases split
    | some pair =>
      obtain ⟨first, rest⟩ := pair
      have shaped := conjunct?_eq_some.mp split
      subst shaped
      simp only [Option.map_eq_some_iff]
      constructor
      · rintro ⟨tail, inner, rfl⟩
        obtain ⟨length, joined⟩ := ih.mp inner
        cases tail with
        | nil => simp at length
        | cons next more =>
          simp only [List.length_cons] at length ⊢
          exact ⟨by omega, by simp [Shape.conjunction, joined]⟩
      · rintro ⟨length, joined⟩
        cases parts with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | nil => simp at length
          | cons next more =>
            simp [Shape.conjunction] at joined
            obtain ⟨rfl, inner⟩ := joined
            exact ⟨next :: more, ih.mpr ⟨by simp only [List.length_cons] at length ⊢; omega, inner⟩, rfl⟩

theorem subst_tuple {replaceable : Name → Bool} {σ : Witnesses} (statements : List Shape) :
    (tuple statements).subst replaceable σ = tuple (statements.map (·.subst replaceable σ)) := by
  induction statements with
  | nil => rfl
  | cons statement rest ih => simp [tuple, Shape.subst, ih]

theorem tuple_inj {left right : List Shape} : tuple left = tuple right ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [tuple]
  | cons statement rest ih =>
    cases right with
    | nil => simp [tuple]
    | cons other more => simp [tuple, ih, and_comm]

theorem plainKill_eq_true {replaceable : Name → Bool} {headline kill : Shape} :
    plainKill replaceable headline kill = true ↔
      ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ headline.subst replaceable σ ≠ headline ∧
        kill = (headline.subst replaceable σ).negation := by
  unfold plainKill
  split
  · rename_i rejected found
    rw [negated?_eq_some] at found
    subst found
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Shape.witnesses?_isSome_iff]
    constructor
    · rintro ⟨different, σ, closed, instantiates⟩
      exact ⟨σ, closed, by rw [instantiates]; exact different, by rw [instantiates]⟩
    · rintro ⟨σ, closed, changed, negated⟩
      have same : rejected = headline.subst replaceable σ := by
        simpa [Shape.negation] using negated
      subst same
      exact ⟨changed, σ, closed, rfl⟩
  · rename_i missing
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro σ _ _ negated
    exact absurd (negated?_eq_some.mpr negated) (by simp [missing])

theorem independenceKill_eq_true {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape} :
    independenceKill replaceable headline others kill = true ↔
      ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ headline.subst replaceable σ ≠ headline ∧
        others ≠ [] ∧
          kill = Shape.conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) := by
  unfold independenceKill
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨nonempty, matched⟩
    split at matched
    · rename_i first rest split
      obtain ⟨-, joined⟩ := conjuncts_eq_some.mp split
      split at matched
      · rename_i rejected negated
        rw [negated?_eq_some] at negated
        subst negated
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Shape.witnesses?_isSome_iff] at matched
        obtain ⟨different, σ, closed, instantiates⟩ := matched
        rw [subst_tuple, List.map_cons, tuple_inj, List.cons.injEq] at instantiates
        obtain ⟨headed, rested⟩ := instantiates
        refine ⟨σ, closed, by rw [headed]; exact different, nonempty, ?_⟩
        rw [headed, rested, joined]
      · cases matched
    · cases matched
  · rintro ⟨σ, closed, changed, nonempty, joined⟩
    have split : conjuncts others.length kill =
        some ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)) :=
      conjuncts_eq_some.mpr ⟨by simp, joined.symm⟩
    have negated : negated? (headline.subst replaceable σ).negation = some (headline.subst replaceable σ) :=
      negated?_eq_some.mpr rfl
    refine ⟨nonempty, ?_⟩
    rw [split]
    simp only [negated, Bool.and_eq_true, bne_iff_ne, ne_eq, Shape.witnesses?_isSome_iff]
    exact ⟨changed, σ, closed, by rw [subst_tuple, List.map_cons]⟩

theorem killedBy_eq_true {replaceable : Name → Bool} {headline kill : Shape} {others : List Shape} :
    killedBy replaceable headline others kill = true ↔ headline.KilledBy replaceable others kill := by
  unfold killedBy Shape.KilledBy
  rw [Bool.or_eq_true, plainKill_eq_true, independenceKill_eq_true]
  constructor
  · rintro (⟨σ, closed, changed, negated⟩ | ⟨σ, closed, changed, nonempty, joined⟩)
    · exact ⟨σ, closed, changed, .inl negated⟩
    · exact ⟨σ, closed, changed, .inr ⟨nonempty, joined⟩⟩
  · rintro ⟨σ, closed, changed, negated | ⟨nonempty, joined⟩⟩
    · exact .inl ⟨σ, closed, changed, negated⟩
    · exact .inr ⟨σ, closed, changed, nonempty, joined⟩

end SoftwareChallenge.Statement

module

public import SoftwareChallenge.CoreCode.Rules.Statement
import all SoftwareChallenge.CoreCode.Rules.Statement
import SoftwareChallenge.Solution.Format
import SoftwareChallenge.Solution.Admits
import all SoftwareChallenge.CoreCode.Classify

public section

namespace SoftwareChallenge

open Lean

namespace Statement

attribute [local simp] Array.any_eq_true' Array.all_eq_true' Array.any_eq_false' Array.all_eq_false'

attribute [-simp] Array.any_eq_true Array.all_eq_true Array.any_eq_false Array.all_eq_false

theorem builds_eq_true {lake : LakeFacts} {module : Name} : builds lake module = true ↔ lake.Builds module := by
  simp [builds, LakeFacts.Builds]

theorem namedSolution_eq_true {name : Name} : namedSolution name = true ↔ Name.NamedSolution name := by
  cases name <;> simp [namedSolution, Name.NamedSolution]

theorem mem_solutions {lake : LakeFacts} {name : Name} :
    name ∈ solutions lake ↔ ∃ source ∈ lake.modules, Name.NamedSolution source.module ∧ source.module = name := by
  simp [solutions, namedSolution_eq_true, and_assoc]

theorem solution?_isSome {lake : LakeFacts} : (solution? lake).isSome = true ↔ lake.OneSolution := by
  unfold solution? LakeFacts.OneSolution
  constructor
  · intro found
    split at found
    · rename_i first rest listed
      split at found
      · rename_i same
        have firstIn : first ∈ solutions lake := by
          rw [← Array.mem_toList_iff, listed]
          exact List.mem_cons_self
        obtain ⟨solution, member, named, rfl⟩ := mem_solutions.mp firstIn
        refine ⟨solution, member, named, fun other otherMember otherNamed => ?_⟩
        have otherIn : other.module ∈ solutions lake := mem_solutions.mpr ⟨other, otherMember, otherNamed, rfl⟩
        rw [← Array.mem_toList_iff, listed, List.mem_cons] at otherIn
        rcases otherIn with equal | inRest
        · exact equal
        · simpa using List.all_eq_true.mp same _ inRest
      · cases found
    · cases found
  · rintro ⟨solution, member, named, unique⟩
    have solutionIn : solution.module ∈ solutions lake := mem_solutions.mpr ⟨solution, member, named, rfl⟩
    have allSame : ∀ name ∈ (solutions lake).toList, name = solution.module := by
      intro name inList
      obtain ⟨other, otherMember, otherNamed, rfl⟩ := mem_solutions.mp (Array.mem_toList_iff.mp inList)
      exact unique other otherMember otherNamed
    split
    · rename_i first rest listed
      rw [listed] at allSame
      have firstSame := allSame first List.mem_cons_self
      have restSame : rest.all (· == first) = true := List.all_eq_true.mpr fun name inRest => by
        simp [allSame name (List.mem_cons_of_mem _ inRest), firstSame]
      simp [restSame]
    · rename_i listed
      rw [← Array.mem_toList_iff, listed] at solutionIn
      cases solutionIn

theorem challengeErrors_eq_empty {lake : LakeFacts} {challenge : ChallengeFacts} :
    challengeErrors lake challenge = #[] ↔
      ∃ candidate, lake.challengeCandidates = #[candidate] ∧ candidate.module = challenge.module := by
  have singleton : ∀ candidate, lake.challengeCandidates = #[candidate] ↔
      lake.challengeCandidates.toList = [candidate] := fun candidate => by
    rw [← Array.toList_inj]
  simp only [singleton]
  unfold challengeErrors
  split
  · rename_i candidate listed
    simp only [listed, List.cons.injEq, and_true]
    by_cases same : candidate.module = challenge.module
    · simp [same]
    · simp [same]
  · rename_i different
    constructor
    · intro refused
      simp at refused
    · rintro ⟨candidate, listed, -⟩
      exact absurd listed (different candidate)

theorem solutionErrors_eq_empty {lake : LakeFacts} : solutionErrors lake = #[] ↔ lake.OneSolution := by
  unfold solutionErrors
  rw [← solution?_isSome]
  cases (solution? lake).isSome <;> simp

theorem targetErrors_eq_empty {lake : LakeFacts} : targetErrors lake = #[] ↔ `statement ∈ lake.defaultTargets := by
  unfold targetErrors
  by_cases listed : `statement ∈ lake.defaultTargets
  · simp [listed]
  · simp [listed]

theorem programErrors_eq_empty {lake : LakeFacts} :
    programErrors lake = #[] ↔ (lake.defaultExeRoots ≠ #[] →
      (∃ source ∈ lake.modules, Role.ofName source.module = .worldCode) → lake.Program) := by
  unfold programErrors LakeFacts.Program
  by_cases empty : lake.defaultExeRoots = #[]
  · simp [empty]
  · by_cases world : ∃ source ∈ lake.modules, Role.ofName source.module = .worldCode
    · by_cases rooted : ∃ root ∈ lake.defaultExeRoots, Role.ofName root = .worldCode
      · have rootedAny : lake.defaultExeRoots.any (Role.ofName · == .worldCode) = true := by
          simpa [Array.any_eq_true'] using rooted
        simp [rootedAny, rooted]
      · have rootedAny : lake.defaultExeRoots.any (Role.ofName · == .worldCode) = false := by
          simpa [Array.any_eq_false'] using rooted
        have worldAny : lake.modules.any (Role.ofName ·.module == .worldCode) = true := by
          simpa [Array.any_eq_true'] using world
        simp [empty, rootedAny, worldAny, rooted, world]
    · have worldAny : lake.modules.any (Role.ofName ·.module == .worldCode) = false := by
        simpa using world
      simp [worldAny, world]

theorem ownsModule_eq_true {challenge : ChallengeFacts} {module : Name} :
    ownsModule challenge module = true ↔ challenge.Owns module := by
  simp [ownsModule, ChallengeFacts.owns, ChallengeFacts.Owns, Role.Owned, or_assoc]

theorem mem_ownedPaths {lake : LakeFacts} {challenge : ChallengeFacts} {path : String} :
    path ∈ ownedPaths lake challenge ↔ lake.Owned challenge path := by
  simp [ownedPaths, LakeFacts.Owned, ownsModule_eq_true, or_assoc, and_assoc]

theorem digested_eq_true {files : FileFacts} {path : String} :
    digested files path = true ↔ files.Digested path := by
  simp [digested, FileFacts.Digested]

theorem recorded_eq_true {files : FileFacts} {path : String} :
    recorded files path = true ↔ ∃ locked, files.lock = .decoded locked ∧ ∃ entry ∈ locked, entry.path = path := by
  unfold recorded
  cases files.lock with
  | missing => simp
  | unreadable problem => simp
  | decoded locked => simp

theorem digestOf_eq_none {entries : Array Lock.Entry} {path : String} :
    Lock.digestOf entries path = none ↔ ∀ entry ∈ entries, entry.path ≠ path := by
  simp [Lock.digestOf, Array.find?_eq_none]

theorem lockErrors_eq_empty {lake : LakeFacts} {files : FileFacts} {challenge : ChallengeFacts} :
    lockErrors lake files challenge = #[] ↔ files.lock = .missing ∨ files.LockCurrent := by
  unfold lockErrors FileFacts.LockCurrent
  cases locked : files.lock with
  | missing => simp
  | unreadable problem => simp
  | decoded entries => simp [Lock.violations_eq_empty_iff]

theorem digested_of_recorded {files : FileFacts} {path : String} (recordedPath : recorded files path = true)
    (current : files.lock = .missing ∨ files.LockCurrent) : files.Digested path := by
  obtain ⟨locked, decodedLock, entry, entryMember, entryPath⟩ := recorded_eq_true.mp recordedPath
  rcases current with missing | ⟨same, sameDecoded, agree⟩
  · rw [missing] at decodedLock
    cases decodedLock
  · rw [decodedLock, Decoded.decoded.injEq] at sameDecoded
    subst sameDecoded
    have lockedSome : Lock.digestOf locked path ≠ none := by
      rw [ne_eq, digestOf_eq_none]
      intro absent
      exact absent entry entryMember entryPath
    rw [agree path, ne_eq, digestOf_eq_none] at lockedSome
    exact Classical.byContradiction fun absent =>
      lockedSome fun found foundMember foundPath => absent ⟨found, foundMember, foundPath⟩

theorem lockingErrors_eq_empty {lake : LakeFacts} {files : FileFacts} {challenge : ChallengeFacts} :
    lockingErrors lake files challenge = #[] ↔
      (∀ path, lake.Owned challenge path → files.Digested path) ∧ (files.lock = .missing ∨ files.LockCurrent) := by
  simp only [lockingErrors, Array.append_eq_empty_iff, lockErrors_eq_empty, unreadErrors,
    Array.filterMap_eq_empty_iff]
  constructor
  · rintro ⟨unread, current⟩
    refine ⟨fun path owned => ?_, current⟩
    have accepted := unread path (mem_ownedPaths.mpr owned)
    cases digestedPath : digested files path
    · cases recordedPath : recorded files path
      · simp [digestedPath, recordedPath] at accepted
      · exact digested_of_recorded recordedPath current
    · exact digested_eq_true.mp digestedPath
  · rintro ⟨owned, current⟩
    refine ⟨fun path member => ?_, current⟩
    simp [digested_eq_true.mpr (owned path (mem_ownedPaths.mp member))]

theorem specRole_eq_true {module : Name} :
    specRole module = true ↔ Role.ofName module = .coreSpec ∨ Role.ofName module = .worldSpec := by
  simp [specRole]

theorem codeRole_eq_false {module : Name} :
    codeRole module = false ↔ Role.ofName module ≠ .coreCode ∧ Role.ofName module ≠ .worldCode := by
  simp [codeRole]

theorem importErrors_eq_empty {lake : LakeFacts} {challenge : ChallengeFacts} :
    importErrors lake challenge = #[] ↔ ∀ line ∈ challenge.runtimeImports, lake.Builds line.fact.name →
      Role.ofName line.fact.name = .coreSpec ∨ Role.ofName line.fact.name = .worldSpec := by
  simp only [importErrors, Array.filterMap_eq_empty_iff]
  refine forall_congr' fun line => imp_congr_right fun _ => ?_
  rw [← builds_eq_true, ← specRole_eq_true]
  cases builds lake line.fact.name <;> cases specRole line.fact.name <;> simp

theorem closureErrors_eq_empty {lake : LakeFacts} {challenge : ChallengeFacts}
    (noCode : ∀ module ∈ challenge.closure, lake.Builds module →
      Role.ofName module ≠ .coreCode ∧ Role.ofName module ≠ .worldCode) :
    closureErrors lake challenge = #[] := by
  simp only [closureErrors, Array.filterMap_eq_empty_iff]
  intro module member
  cases built : builds lake module
  · simp
  · simp [codeRole_eq_false.mpr (noCode module member (builds_eq_true.mp built))]

theorem noCode_of_closureErrors {lake : LakeFacts} {challenge : ChallengeFacts}
    (closureEmpty : closureErrors lake challenge = #[]) (importEmpty : importErrors lake challenge = #[]) :
    ∀ module ∈ challenge.closure, lake.Builds module →
      Role.ofName module ≠ .coreCode ∧ Role.ofName module ≠ .worldCode := by
  intro module member built
  rw [← codeRole_eq_false]
  cases code : codeRole module
  · rfl
  · exfalso
    have codeRoles : Role.ofName module = .coreCode ∨ Role.ofName module = .worldCode := by
      simpa [codeRole] using code
    cases direct : challenge.runtimeImports.any (·.fact.name == module)
    · simp only [closureErrors, Array.filterMap_eq_empty_iff] at closureEmpty
      have refused := closureEmpty module member
      simp [builds_eq_true.mpr built, code, direct] at refused
    · obtain ⟨line, inImports, named⟩ := Array.any_eq_true'.mp direct
      rw [beq_iff_eq] at named
      have spec := (importErrors_eq_empty.mp importEmpty) line inImports (by rw [named]; exact built)
      rw [named] at spec
      rcases codeRoles with coded | coded <;> rcases spec with specced | specced <;> rw [coded] at specced <;>
        cases specced

theorem filledErrors_eq_empty {challenge : ChallengeFacts} : filledErrors challenge = #[] ↔ challenge.filled = #[] := by
  simp [filledErrors]

theorem axiomErrors_eq_empty {challenge : ChallengeFacts} : axiomErrors challenge = #[] ↔ challenge.axioms = #[] := by
  simp [axiomErrors]

theorem privateErrors_eq_empty {challenge : ChallengeFacts} :
    privateErrors challenge = #[] ↔ ∀ target ∈ challenge.targets, target.constant.isPrivate = false := by
  simp [privateErrors]

theorem plainErrors_empty {challenge : ChallengeFacts}
    (plainNames : ∀ target ∈ challenge.targets, Name.Plain target.constant.name) : plainErrors challenge = #[] := by
  simp only [plainErrors, Array.filterMap_eq_empty_iff]
  intro target member
  simp [plain_eq_true.mpr (plainNames target member)]

theorem plain_of_plainErrors {challenge : ChallengeFacts} (plainEmpty : plainErrors challenge = #[])
    (privateEmpty : privateErrors challenge = #[]) : ∀ target ∈ challenge.targets, Name.Plain target.constant.name := by
  intro target member
  have published := (privateErrors_eq_empty.mp privateEmpty) target member
  simp only [plainErrors, Array.filterMap_eq_empty_iff] at plainEmpty
  have accepted := plainEmpty target member
  rw [← plain_eq_true]
  cases named : plain target.constant.name
  · simp [published, named] at accepted
  · rfl

theorem auxiliaryErrors_eq_empty {challenge : ChallengeFacts} :
    auxiliaryErrors challenge = #[] ↔
      ∀ target ∈ challenge.targets, ∀ auxiliary ∈ target.auxiliaries, auxiliary.isPrivate = false := by
  simp [auxiliaryErrors, Array.flatMap_eq_empty_iff]

theorem listToArray_eq_empty {α : Type} {list : List α} : list.toArray = #[] ↔ list = [] := by
  constructor
  · intro empty
    simpa using congrArg Array.toList empty
  · rintro rfl
    rfl

theorem duplicatesFrom_eq_nil {seen entries : List (Name × Shape)} :
    duplicatesFrom seen entries = [] ↔
      (entries.map (·.2)).Nodup ∧ ∀ entry ∈ entries, ∀ earlier ∈ seen, earlier.2 ≠ entry.2 := by
  induction entries generalizing seen with
  | nil => simp [duplicatesFrom]
  | cons entry rest ih =>
    obtain ⟨name, statement⟩ := entry
    simp only [duplicatesFrom]
    split
    · rename_i earlier found
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ apart
      exact apart (name, statement) List.mem_cons_self earlier (List.mem_of_find?_eq_some found)
        (by simpa using List.find?_some found)
    · rename_i missing
      rw [ih]
      rw [List.find?_eq_none] at missing
      constructor
      · rintro ⟨nodup, apart⟩
        refine ⟨List.nodup_cons.mpr ⟨fun inRest => ?_, nodup⟩, fun entry member earlier inSeen => ?_⟩
        · obtain ⟨other, otherMember, same⟩ := List.mem_map.mp inRest
          exact apart other otherMember (name, statement) (List.mem_append_right _ List.mem_cons_self) same.symm
        · rcases List.mem_cons.mp member with rfl | inRest
          · intro same
            exact missing earlier inSeen (by simp [same])
          · exact apart entry inRest earlier (List.mem_append_left _ inSeen)
      · rintro ⟨nodup, apart⟩
        obtain ⟨fresh, nodupRest⟩ := List.nodup_cons.mp nodup
        refine ⟨nodupRest, fun entry member earlier inSeen => ?_⟩
        rcases List.mem_append.mp inSeen with inSeen | isNew
        · exact apart entry (List.mem_cons_of_mem _ member) earlier inSeen
        · rw [List.mem_singleton] at isNew
          subst isNew
          intro same
          exact fresh (List.mem_map.mpr ⟨entry, member, same.symm⟩)

theorem duplicates_eq_nil {challenge : ChallengeFacts} :
    duplicates challenge = [] ↔ (challenge.headlines.toList.map (·.target.constant.type)).Nodup := by
  simp [duplicates, duplicatesFrom_eq_nil, List.map_map, Function.comp_def]

theorem duplicateErrors_eq_empty {challenge : ChallengeFacts} :
    duplicateErrors challenge = #[] ↔ (challenge.headlines.toList.map (·.target.constant.type)).Nodup := by
  rw [← duplicates_eq_nil, duplicateErrors, listToArray_eq_empty, List.map_eq_nil_iff]

theorem mentionsReplaceable_eq_true {challenge : ChallengeFacts} {headline : HeadlineFact} :
    mentionsReplaceable challenge headline = true ↔
      ∃ name, challenge.isReplaceable name = true ∧ headline.target.constant.type.Mentions name := by
  unfold mentionsReplaceable
  rw [List.any_eq_true]
  exact exists_congr fun name => by rw [Shape.mem_constants, and_comm]

theorem target_mem_targets {challenge : ChallengeFacts} {headline : HeadlineFact}
    (member : headline ∈ challenge.headlines) : headline.target ∈ challenge.targets := by
  simp only [ChallengeFacts.targets, ChallengeFacts.theorems, Array.mem_append, Array.mem_map]
  exact .inl (.inl (.inl ⟨headline, member, rfl⟩))

theorem laterDuplicate_eq_false {challenge : ChallengeFacts} {headline : HeadlineFact}
    (duplicateEmpty : duplicateErrors challenge = #[]) : laterDuplicate challenge headline = false := by
  have noDuplicates : duplicates challenge = [] := by
    rw [duplicates_eq_nil, ← duplicateErrors_eq_empty]
    exact duplicateEmpty
  simp [laterDuplicate, noDuplicates]

theorem unreproducible_eq_false {challenge : ChallengeFacts} {headline : HeadlineFact}
    (member : headline ∈ challenge.headlines) (auxiliaryEmpty : auxiliaryErrors challenge = #[]) :
    unreproducible headline = false := by
  have published := (auxiliaryErrors_eq_empty.mp auxiliaryEmpty) headline.target (target_mem_targets member)
  exact Array.any_eq_false'.mpr fun auxiliary inAuxiliaries => by simp [published auxiliary inAuxiliaries]

theorem killsAnother_eq_false {challenge : ChallengeFacts} {headline : HeadlineFact}
    (member : headline ∈ challenge.headlines)
    (marked : ∀ headline ∈ challenge.headlines, ∀ other ∈ challenge.headlines,
      ¬ headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
        other.target.constant.type) : killsAnother challenge headline = false := by
  simp only [killsAnother, Array.any_eq_false']
  intro other otherMember killed
  exact marked other otherMember headline member (killedBy_eq_true.mp killed)

theorem unmarkedErrors_empty {challenge : ChallengeFacts}
    (marked : ∀ headline ∈ challenge.headlines, ∀ other ∈ challenge.headlines,
      ¬ headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
        other.target.constant.type) : unmarkedErrors challenge = #[] := by
  simp only [unmarkedErrors, Array.flatMap_eq_empty_iff, Array.map_eq_empty_iff, Array.filter_eq_empty_iff,
    Bool.and_eq_true, not_and]
  intro headline headlineMember kill killMember _ killed
  exact marked headline (Array.mem_filter.mp headlineMember).1 kill killMember (killedBy_eq_true.mp killed)

theorem marked_of_unmarkedErrors {challenge : ChallengeFacts} (unmarkedEmpty : unmarkedErrors challenge = #[])
    (duplicateEmpty : duplicateErrors challenge = #[]) :
    ∀ headline ∈ challenge.headlines, ∀ other ∈ challenge.headlines,
      ¬ headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
        other.target.constant.type := by
  intro headline member other otherMember killed
  simp only [unmarkedErrors, Array.flatMap_eq_empty_iff, Array.map_eq_empty_iff, Array.filter_eq_empty_iff,
    Bool.and_eq_true, not_and] at unmarkedEmpty
  have kept : headline ∈ challenge.headlines.filter (!laterDuplicate challenge ·) :=
    Array.mem_filter.mpr ⟨member, by simp [laterDuplicate_eq_false duplicateEmpty]⟩
  exact unmarkedEmpty headline kept other otherMember (by simp [laterDuplicate_eq_false duplicateEmpty])
    (killedBy_eq_true.mpr killed)

theorem mentionErrors_empty {challenge : ChallengeFacts}
    (mentions : ∀ headline ∈ challenge.headlines,
      ∃ name, challenge.isReplaceable name = true ∧ headline.target.constant.type.Mentions name) :
    mentionErrors challenge = #[] := by
  simp only [mentionErrors, Array.filterMap_eq_empty_iff]
  intro headline member
  simp [mentionsReplaceable_eq_true.mpr (mentions headline member)]

theorem mentions_of_mentionErrors {challenge : ChallengeFacts} (mentionEmpty : mentionErrors challenge = #[])
    (duplicateEmpty : duplicateErrors challenge = #[]) (auxiliaryEmpty : auxiliaryErrors challenge = #[])
    (unmarkedEmpty : unmarkedErrors challenge = #[]) :
    ∀ headline ∈ challenge.headlines,
      ∃ name, challenge.isReplaceable name = true ∧ headline.target.constant.type.Mentions name := by
  intro headline member
  simp only [mentionErrors, Array.filterMap_eq_empty_iff] at mentionEmpty
  have accepted := mentionEmpty headline member
  rw [laterDuplicate_eq_false duplicateEmpty, unreproducible_eq_false member auxiliaryEmpty,
    killsAnother_eq_false member (marked_of_unmarkedErrors unmarkedEmpty duplicateEmpty)] at accepted
  rw [← mentionsReplaceable_eq_true]
  cases found : mentionsReplaceable challenge headline
  · simp [found] at accepted
  · rfl

theorem settled_eq_false {challenge : ChallengeFacts} {headline : HeadlineFact}
    (member : headline ∈ challenge.headlines)
    (duplicateEmpty : duplicateErrors challenge = #[]) (auxiliaryEmpty : auxiliaryErrors challenge = #[])
    (mentions : ∀ headline ∈ challenge.headlines,
      ∃ name, challenge.isReplaceable name = true ∧ headline.target.constant.type.Mentions name) :
    settled challenge headline = false := by
  simp [settled, laterDuplicate_eq_false duplicateEmpty, unreproducible_eq_false member auxiliaryEmpty,
    mentionsReplaceable_eq_true.mpr (mentions headline member)]

theorem unmarked_eq_false {challenge : ChallengeFacts} {headline : HeadlineFact}
    (member : headline ∈ challenge.headlines)
    (marked : ∀ headline ∈ challenge.headlines, ∀ other ∈ challenge.headlines,
      ¬ headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
        other.target.constant.type) : unmarked challenge headline = false := by
  simp only [unmarked, killsAnother_eq_false member marked, Bool.or_false, Array.any_eq_false']
  intro other otherMember killed
  exact marked headline member other otherMember (killedBy_eq_true.mp killed)

theorem hasKill_eq_true {challenge : ChallengeFacts} {headline : Name} :
    hasKill challenge headline = true ↔ ∃ kill ∈ challenge.kills, kill.headline = headline := by
  simp [hasKill]

theorem noKillErrors_empty {challenge : ChallengeFacts}
    (killed : ∀ headline ∈ challenge.headlines,
      ∃ kill ∈ challenge.kills, kill.headline = headline.target.constant.name) :
    noKillErrors challenge = #[] := by
  simp only [noKillErrors, Array.filterMap_eq_empty_iff]
  intro headline member
  simp [hasKill_eq_true.mpr (killed headline member)]

theorem killed_of_noKillErrors {challenge : ChallengeFacts} (noKillEmpty : noKillErrors challenge = #[])
    (duplicateEmpty : duplicateErrors challenge = #[]) (auxiliaryEmpty : auxiliaryErrors challenge = #[])
    (mentions : ∀ headline ∈ challenge.headlines,
      ∃ name, challenge.isReplaceable name = true ∧ headline.target.constant.type.Mentions name)
    (marked : ∀ headline ∈ challenge.headlines, ∀ other ∈ challenge.headlines,
      ¬ headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
        other.target.constant.type) :
    ∀ headline ∈ challenge.headlines, ∃ kill ∈ challenge.kills, kill.headline = headline.target.constant.name := by
  intro headline member
  simp only [noKillErrors, Array.filterMap_eq_empty_iff] at noKillEmpty
  have accepted := noKillEmpty headline member
  rw [settled_eq_false member duplicateEmpty auxiliaryEmpty mentions, unmarked_eq_false member marked] at accepted
  cases found : hasKill challenge headline.target.constant.name
  · simp [found] at accepted
  · exact hasKill_eq_true.mp found

theorem killErrors_empty {challenge : ChallengeFacts}
    (named : ∀ kill ∈ challenge.kills, ∃ headline ∈ challenge.headlines, headline.target.constant.name = kill.headline)
    (reject : ∀ kill ∈ challenge.kills, ∀ headline ∈ challenge.headlines,
      kill.headline = headline.target.constant.name →
        headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
          kill.target.constant.type) :
    killErrors challenge = #[] := by
  simp only [killErrors, Array.flatMap_eq_empty_iff]
  intro kill member
  obtain ⟨headline, headlineMember, same⟩ := named kill member
  have inFilter : headline ∈ challenge.headlines.filter (·.target.constant.name == kill.headline) :=
    Array.mem_filter.mpr ⟨headlineMember, by simp [same]⟩
  split
  · rename_i empty
    rw [Array.isEmpty_iff.mp empty] at inFilter
    simp at inFilter
  · rw [Array.filterMap_eq_empty_iff]
    intro candidate candidateMember
    obtain ⟨candidateHeadline, candidateNamed⟩ := Array.mem_filter.mp candidateMember
    have candidateSame : candidate.target.constant.name = kill.headline := by simpa using candidateNamed
    have killedIt : killsHeadline challenge candidate kill.target.constant.type = true :=
      killedBy_eq_true.mpr (reject kill member candidate candidateHeadline candidateSame.symm)
    simp [killedIt]

theorem killed_of_killErrors {challenge : ChallengeFacts} (killEmpty : killErrors challenge = #[])
    (duplicateEmpty : duplicateErrors challenge = #[]) (auxiliaryEmpty : auxiliaryErrors challenge = #[])
    (mentions : ∀ headline ∈ challenge.headlines,
      ∃ name, challenge.isReplaceable name = true ∧ headline.target.constant.type.Mentions name) :
    (∀ kill ∈ challenge.kills, ∃ headline ∈ challenge.headlines, headline.target.constant.name = kill.headline) ∧
      ∀ kill ∈ challenge.kills, ∀ headline ∈ challenge.headlines, kill.headline = headline.target.constant.name →
        headline.target.constant.type.KilledBy challenge.isReplaceable (challenge.othersOf headline)
          kill.target.constant.type := by
  simp only [killErrors, Array.flatMap_eq_empty_iff] at killEmpty
  constructor
  · intro kill member
    have accepted := killEmpty kill member
    split at accepted
    · simp at accepted
    · rename_i nonempty
      refine Classical.byContradiction fun absent => nonempty ?_
      rw [Array.isEmpty_iff, Array.filter_eq_empty_iff]
      intro headline headlineMember named
      exact absent ⟨headline, headlineMember, by simpa using named⟩
  · intro kill member headline headlineMember same
    have accepted := killEmpty kill member
    have inFilter : headline ∈ challenge.headlines.filter (·.target.constant.name == kill.headline) :=
      Array.mem_filter.mpr ⟨headlineMember, by simp [same]⟩
    split at accepted
    · rename_i empty
      rw [Array.isEmpty_iff.mp empty] at inFilter
      simp at inFilter
    · rw [Array.filterMap_eq_empty_iff] at accepted
      have judged := accepted headline inFilter
      rw [settled_eq_false headlineMember duplicateEmpty auxiliaryEmpty mentions, Bool.false_or] at judged
      cases killedIt : killsHeadline challenge headline kill.target.constant.type
      · exact absurd judged (by simp [killedIt]; split <;> simp)
      · exact killedBy_eq_true.mp killedIt

theorem needsWitness_eq_true {challenge : ChallengeFacts} {headline : HeadlineFact} :
    needsWitness challenge headline = true ↔
      ∃ index, ¬ headline.Claim challenge.claims index ∧ headline.Mentions challenge.isReplaceable index := by
  unfold needsWitness HeadlineFact.binders
  rw [List.any_eq_true]
  constructor
  · rintro ⟨summarized, member, holds⟩
    obtain ⟨index, binder, found, rfl⟩ := Telescope.mem_summary.mp member
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Telescope.binderAt] at holds
    exact ⟨index, (Telescope.kindAt_ne_claim_iff found).mp holds.1, binder, found,
      Telescope.mentions_any_iff.mp holds.2⟩
  · rintro ⟨index, notClaim, binder, found, mentions⟩
    refine ⟨Telescope.binderAt challenge.isClaim challenge.isReplaceable headline.telescope index binder,
      Telescope.mem_summary.mpr ⟨index, binder, found, rfl⟩, ?_⟩
    simp only [Telescope.binderAt, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨(Telescope.kindAt_ne_claim_iff found).mpr notClaim, Telescope.mentions_any_iff.mpr mentions⟩

theorem misstated_eq_false {challenge : ChallengeFacts} {witness : WitnessFact}
    (stated : ∀ headline ∈ challenge.headlines, headline.target.constant.name = witness.headline →
      witness.target.constant.type = headline.expectedWitness challenge) : misstated challenge witness = false := by
  unfold misstated
  rw [Bool.eq_false_iff]
  intro found
  obtain ⟨headline, member, matched⟩ := Array.any_eq_true'.mp found
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at matched
  exact matched.2 (stated headline member matched.1)

theorem stated_of_misstated {challenge : ChallengeFacts} {witness : WitnessFact}
    (accepted : misstated challenge witness = false) :
    ∀ headline ∈ challenge.headlines, headline.target.constant.name = witness.headline →
      witness.target.constant.type = headline.expectedWitness challenge := by
  intro headline member named
  apply Classical.byContradiction
  intro differs
  have found : misstated challenge witness = true :=
    Array.any_eq_true'.mpr ⟨headline, member, by simp [named, differs]⟩
  simp [found] at accepted

theorem witnessErrors_empty {challenge : ChallengeFacts}
    (witnessed : ∀ headline ∈ challenge.headlines,
      (∃ index, ¬ headline.Claim challenge.claims index ∧ headline.Mentions challenge.isReplaceable index) →
        ∃ witness ∈ challenge.witnesses, witness.headline = headline.target.constant.name)
    (derived : ∀ witness ∈ challenge.witnesses, witness.derived = true)
    (stated : ∀ witness ∈ challenge.witnesses, ∀ headline ∈ challenge.headlines,
      headline.target.constant.name = witness.headline →
        witness.target.constant.type = headline.expectedWitness challenge) : witnessErrors challenge = #[] := by
  simp only [witnessErrors, Array.append_eq_empty_iff, Array.filterMap_eq_empty_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro headline member
    cases needs : needsWitness challenge headline
    · simp
    · obtain ⟨witness, witnessMember, named⟩ := witnessed headline member (needsWitness_eq_true.mp needs)
      have found : challenge.witnesses.any (·.headline == headline.target.constant.name) = true :=
        Array.any_eq_true'.mpr ⟨witness, witnessMember, by simp [named]⟩
      simp [found]
  · intro witness member
    simp [derived witness member]
  · intro witness member
    simp [misstated_eq_false (stated witness member)]

theorem witnessed_of_witnessErrors {challenge : ChallengeFacts} (witnessEmpty : witnessErrors challenge = #[])
    (killed : ∀ headline ∈ challenge.headlines,
      ∃ kill ∈ challenge.kills, kill.headline = headline.target.constant.name) :
    (∀ headline ∈ challenge.headlines,
      (∃ index, ¬ headline.Claim challenge.claims index ∧ headline.Mentions challenge.isReplaceable index) →
        ∃ witness ∈ challenge.witnesses, witness.headline = headline.target.constant.name) ∧
      (∀ witness ∈ challenge.witnesses, witness.derived = true) ∧
      ∀ witness ∈ challenge.witnesses, ∀ headline ∈ challenge.headlines,
        headline.target.constant.name = witness.headline →
          witness.target.constant.type = headline.expectedWitness challenge := by
  simp only [witnessErrors, Array.append_eq_empty_iff, Array.filterMap_eq_empty_iff] at witnessEmpty
  obtain ⟨⟨missing, predeclared⟩, misstatedEmpty⟩ := witnessEmpty
  refine ⟨?_, ?_, ?_⟩
  · intro headline member needs
    have accepted := missing headline member
    rw [needsWitness_eq_true.mpr needs, hasKill_eq_true.mpr (killed headline member)] at accepted
    cases found : challenge.witnesses.any (·.headline == headline.target.constant.name)
    · simp [found] at accepted
    · obtain ⟨witness, witnessMember, same⟩ := Array.any_eq_true'.mp found
      exact ⟨witness, witnessMember, by simpa using same⟩
  · intro witness member
    have accepted := predeclared witness member
    cases stated : witness.derived
    · simp [stated] at accepted
    · rfl
  · intro witness member
    have accepted := misstatedEmpty witness member
    cases judged : misstated challenge witness
    · exact stated_of_misstated judged
    · simp [judged] at accepted

theorem holeErrors_eq_empty {challenge : ChallengeFacts} :
    holeErrors challenge = #[] ↔ ∀ hole ∈ challenge.holes,
      ∃ headline ∈ challenge.headlines, headline.target.constant.type.Mentions hole.constant.name := by
  simp only [holeErrors, Array.filterMap_eq_empty_iff]
  refine forall_congr' fun hole => imp_congr_right fun _ => ?_
  have mentionedBy : challenge.headlines.any (fun headline =>
      headline.target.constant.type.constants.contains hole.constant.name) = true ↔
      ∃ headline ∈ challenge.headlines, headline.target.constant.type.Mentions hole.constant.name := by
    simp [Shape.mem_constants]
  rw [← mentionedBy]
  cases challenge.headlines.any _ <;> simp

theorem hypothesisErrors_eq_empty {challenge : ChallengeFacts} :
    hypothesisErrors challenge = #[] ↔ ∀ headline ∈ challenge.headlines, ∀ index binder,
      headline.telescope[index]? = some binder → headline.Precondition challenge.claims index → binder.Open index := by
  simp only [hypothesisErrors, Array.flatMap_eq_empty_iff, listToArray_eq_empty, List.map_eq_nil_iff,
    closedHypotheses, List.filter_eq_nil_iff]
  refine forall₂_congr fun headline _ => ?_
  constructor
  · intro opened index binder found precondition
    have kept := opened (binder, index) (List.mem_zipIdx_iff_getElem?.mpr found)
    simp only [closedHypothesis, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, not_and] at kept
    exact Telescope.refersAt_ne_nil_iff.mp (kept ((Telescope.kindAt_eq_precondition_iff found).mpr precondition))
  · rintro opened ⟨binder, index⟩ member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    simp only [closedHypothesis, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, not_and]
    intro precondition
    exact Telescope.refersAt_ne_nil_iff.mpr
      (opened index binder found ((Telescope.kindAt_eq_precondition_iff found).mp precondition))

theorem isForeignFunction_eq_true {challenge : ChallengeFacts} {name : Name} :
    isForeignFunction challenge name = true ↔ challenge.Foreign name := by
  simp [isForeignFunction, ChallengeFacts.Foreign, ChallengeFacts.isReplaceable]

theorem mem_constraining {challenge : ChallengeFacts} {headline : HeadlineFact} {name : Name} {binder : BinderFact}
    {index : Nat} :
    (binder, index) ∈ constraining challenge headline name ↔
      headline.ClaimConstrains challenge.claims index binder name := by
  unfold constraining HeadlineFact.ClaimConstrains
  rw [List.mem_filter, List.mem_zipIdx_iff_getElem?]
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, Shape.mem_constants]
  constructor
  · rintro ⟨found, claimed, mentions⟩
    exact ⟨found, (Telescope.kindAt_eq_claim_iff found).mp claimed, mentions⟩
  · rintro ⟨found, claimed, mentions⟩
    exact ⟨found, (Telescope.kindAt_eq_claim_iff found).mpr claimed, mentions⟩

theorem unpremisedClaim?_eq_none {challenge : ChallengeFacts} {headline : HeadlineFact} {name : Name} :
    unpremisedClaim? challenge headline name = none ↔
      ((∃ claim claimed, headline.ClaimConstrains challenge.claims claim claimed name ∧ claimed.Open claim) →
        ∃ law stated, headline.ClaimConstrains challenge.claims law stated name ∧ ¬ stated.Open law) := by
  unfold unpremisedClaim?
  dsimp only
  split
  · rename_i premised
    obtain ⟨⟨stated, law⟩, member, closed⟩ := List.any_eq_true.mp premised
    refine ⟨fun _ _ => ⟨law, stated, mem_constraining.mp member, fun opened => ?_⟩, fun _ => rfl⟩
    exact Telescope.refersAt_ne_nil_iff.mpr opened (List.isEmpty_iff.mp closed)
  · rename_i unpremised
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    constructor
    · rintro absent ⟨claim, claimed, constrains, opened⟩
      have rejected := absent (claimed, claim) (mem_constraining.mpr constrains)
      simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Classical.not_not] at rejected
      exact absurd rejected (Telescope.refersAt_ne_nil_iff.mpr opened)
    · intro implies pair member opened
      obtain ⟨claimed, claim⟩ := pair
      have named : (Telescope.refersAt claim claimed).isEmpty = false := by simpa using opened
      obtain ⟨law, stated, constrains, closed⟩ :=
        implies ⟨claim, claimed, mem_constraining.mp member,
          Telescope.refersAt_ne_nil_iff.mp (List.isEmpty_eq_false_iff.mp named)⟩
      have empty : Telescope.refersAt law stated = [] :=
        Classical.byContradiction fun nonempty => closed (Telescope.refersAt_ne_nil_iff.mp nonempty)
      exact unpremised (List.any_eq_true.mpr ⟨(stated, law), mem_constraining.mpr constrains, by simp [empty]⟩)

theorem unprovableErrors_eq_empty {challenge : ChallengeFacts} :
    unprovableErrors challenge = #[] ↔ ∀ headline ∈ challenge.headlines, ∀ index binder name,
      headline.telescope[index]? = some binder → headline.Precondition challenge.claims index →
      challenge.Foreign name → binder.meaning.Mentions name →
      (∃ claim claimed, headline.ClaimConstrains challenge.claims claim claimed name ∧ claimed.Open claim) →
        ∃ law stated, headline.ClaimConstrains challenge.claims law stated name ∧ ¬ stated.Open law := by
  simp only [unprovableErrors, Array.flatMap_eq_empty_iff, listToArray_eq_empty, unprovableWitnesses,
    List.flatMap_eq_nil_iff]
  refine forall₂_congr fun headline _ => ?_
  constructor
  · intro accepted index binder name found precondition foreign mentions
    have judged := accepted (binder, index) (List.mem_zipIdx_iff_getElem?.mpr found)
    have preconditioned : Telescope.kindAt challenge.isClaim headline.telescope index binder = .precondition :=
      (Telescope.kindAt_eq_precondition_iff found).mpr precondition
    simp only [preconditioned, beq_self_eq_true, ↓reduceIte, List.filterMap_eq_nil_iff] at judged
    have listed : name ∈ (binder.meaning.constants.filter (isForeignFunction challenge)).eraseDups := by
      rw [List.mem_eraseDups, List.mem_filter]
      exact ⟨Shape.mem_constants.mpr mentions, isForeignFunction_eq_true.mpr foreign⟩
    have unpremised := judged name listed
    rw [Option.map_eq_none_iff, unpremisedClaim?_eq_none] at unpremised
    exact unpremised
  · intro holds pair member
    obtain ⟨binder, index⟩ := pair
    have found := List.mem_zipIdx_iff_getElem?.mp member
    split
    · rename_i preconditioned
      rw [List.filterMap_eq_nil_iff]
      intro name listed
      rw [List.mem_eraseDups, List.mem_filter, Shape.mem_constants, isForeignFunction_eq_true] at listed
      rw [Option.map_eq_none_iff, unpremisedClaim?_eq_none]
      exact holds index binder name found
        ((Telescope.kindAt_eq_precondition_iff found).mp (beq_iff_eq.mp preconditioned)) listed.2 listed.1
    · rfl

theorem ownedViolationErrors_eq_empty {lake : LakeFacts} {challenge : ChallengeFacts} :
    ownedViolationErrors lake challenge = #[] ↔
      lake.project.Admits (challenge.owned.inventory.restrictedTo challenge.owns) := by
  rw [ownedViolationErrors, Array.map_eq_empty_iff, ownedInventory, Project.violations_eq_empty_iff_admits]

theorem specImportErrors_eq_empty {lake : LakeFacts} {challenge : ChallengeFacts} :
    specImportErrors lake challenge = #[] ↔ ∀ fact ∈ challenge.owned.inventory.modules,
      (Role.ofName fact.name).Owned → ∀ dependency ∈ fact.imports, dependency.comptime = true →
        lake.Builds dependency.name → challenge.Owns dependency.name := by
  simp only [specImportErrors, Array.flatMap_eq_empty_iff]
  refine forall₂_congr fun fact _ => ?_
  by_cases spec : specRole fact.name = true
  · have owned : (Role.ofName fact.name).Owned := specRole_eq_true.mp spec
    simp only [spec, ite_true, Array.filterMap_eq_empty_iff, owned, true_implies]
    refine forall₂_congr fun dependency _ => ?_
    rw [← builds_eq_true, ← ownsModule_eq_true]
    cases dependency.comptime <;> cases builds lake dependency.name <;> cases ownsModule challenge dependency.name <;>
      simp
  · have notOwned : ¬ (Role.ofName fact.name).Owned := fun owned => spec (specRole_eq_true.mpr owned)
    simp [spec, notOwned]

theorem claimDeclared_eq_true {lake : LakeFacts} {registration : RegistrationFact} :
    claimDeclared lake registration = true ↔
      registration.home? = some registration.module ∧ lake.project.role? registration.module = some .worldSpec := by
  simp [claimDeclared]

theorem ownedClaimErrors_eq_empty {lake : LakeFacts} {challenge : ChallengeFacts} :
    ownedClaimErrors lake challenge = #[] ↔ ∀ registration ∈ challenge.owned.registrations,
      challenge.Owns registration.module →
        registration.home? = some registration.module ∧ lake.project.role? registration.module = some .worldSpec := by
  simp only [ownedClaimErrors, Array.filterMap_eq_empty_iff]
  refine forall₂_congr fun registration _ => ?_
  rw [← ownsModule_eq_true, ← claimDeclared_eq_true]
  cases ownsModule challenge registration.module <;> cases claimDeclared lake registration <;> simp

theorem derivedPartialErrors_eq_empty {challenge : ChallengeFacts} :
    derivedPartialErrors challenge = #[] ↔ ∀ fact ∈ challenge.owned.inventory.declarations,
      fact.derivedPartial = true → ¬ challenge.Owns fact.module := by
  simp only [derivedPartialErrors, Array.filterMap_eq_empty_iff]
  refine forall₂_congr fun fact _ => ?_
  rw [← ownsModule_eq_true]
  cases fact.derivedPartial <;> cases ownsModule challenge fact.module <;> simp

theorem ite_empty {condition : Bool} {error : Error} :
    (if condition = true then #[] else #[error]) = #[] ↔ condition = true := by
  cases condition <;> simp

theorem terminationErrors_eq_empty {challenge : ChallengeFacts} :
    terminationErrors challenge = #[] ↔ ∀ termination ∈ challenge.terminating,
      (∃ hole ∈ challenge.holes, hole.constant.name = termination.definition) ∧
      ((∃ headline ∈ challenge.headlines, headline.target.constant.name = termination.headline) ∧
        ∃ kill ∈ challenge.kills, kill.headline = termination.headline) ∧
      ∀ headline ∈ challenge.headlines, headline.target.constant.name = termination.headline →
        headline.target.constant.type.Mentions termination.definition := by
  simp only [terminationErrors, Array.flatMap_eq_empty_iff, Array.append_eq_empty_iff, ite_empty]
  refine forall_congr' fun termination => imp_congr_right fun _ => ?_
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · simp
  · simp [hasKill_eq_true]
  · rw [Array.all_eq_true']
    refine forall_congr' fun headline => imp_congr_right fun _ => ?_
    rw [Bool.or_eq_true, bne_iff_ne, List.contains_iff_mem, Shape.mem_constants]
    constructor
    · rintro (different | mentions) same
      · exact absurd same different
      · exact mentions
    · intro mentions
      by_cases same : headline.target.constant.name = termination.headline
      · exact .inr (mentions same)
      · exact .inl same

theorem isEmpty_eq_false {α : Type} {array : Array α} (nonempty : array ≠ #[]) : array.isEmpty = false := by
  cases emptied : array.isEmpty
  · rfl
  · exact absurd (Array.isEmpty_iff.mp emptied) nonempty

theorem errors_eq_empty {lake : LakeFacts} {files : FileFacts} {challenge : ChallengeFacts} :
    errors lake files challenge = #[] ↔ lockingErrors lake files challenge = #[] ∧ findings lake challenge = #[] := by
  unfold errors
  by_cases found : challengeErrors lake challenge = #[]
  · by_cases locked : lockingErrors lake files challenge = #[]
    · simp [found, locked]
    · simp [found, locked, isEmpty_eq_false locked]
  · simp [found, isEmpty_eq_false found, findings, setupErrors]

theorem setupOf_eq_empty {lake : LakeFacts} :
    setupOf lake = #[] ↔ lake.lintDriver = auditLintDriver ∧ lake.testDriver = auditTestDriver ∧
      lake.builtinLint = none := by
  unfold setupOf lintDriverSetup testDriverSetup builtinLintSetup
  by_cases driven : lake.lintDriver = auditLintDriver <;> by_cases tested : lake.testDriver = auditTestDriver <;>
    cases linted : lake.builtinLint <;> simp [driven, tested]

theorem clean_iff_complete {lake : LakeFacts} {files : FileFacts} {challenge : ChallengeFacts} :
    setupOf lake = #[] ∧ errors lake files challenge = #[] ↔ Complete lake files challenge := by
  rw [setupOf_eq_empty, errors_eq_empty]
  constructor
  · rintro ⟨⟨driven, tested, unlinted⟩, locking, found⟩
    obtain ⟨digestedOwned, current⟩ := lockingErrors_eq_empty.mp locking
    simp only [findings, setupErrors, ownershipErrors, ownerErrors, meaningErrors, statedErrors,
      Array.append_eq_empty_iff, and_assoc] at found
    obtain ⟨challengeEmpty, solutionEmpty, targetEmpty, programEmpty, importEmpty, closureEmpty, filledEmpty,
      axiomEmpty, privateEmpty, plainEmpty, ownedViolationEmpty, specImportEmpty, ownedClaimEmpty, derivedEmpty,
      duplicateEmpty, mentionEmpty, unmarkedEmpty, noKillEmpty, killEmpty, witnessEmpty, holeEmpty, terminationEmpty,
      hypothesisEmpty, unprovableEmpty, auxiliaryEmpty⟩ := found
    have marked := marked_of_unmarkedErrors unmarkedEmpty duplicateEmpty
    have mentions := mentions_of_mentionErrors mentionEmpty duplicateEmpty auxiliaryEmpty unmarkedEmpty
    have killed := killed_of_noKillErrors noKillEmpty duplicateEmpty auxiliaryEmpty mentions marked
    have kills := killed_of_killErrors killEmpty duplicateEmpty auxiliaryEmpty mentions
    have witnesses := witnessed_of_witnessErrors witnessEmpty killed
    have terminations := terminationErrors_eq_empty.mp terminationEmpty
    exact {
      challengeFound := challengeErrors_eq_empty.mp challengeEmpty
      oneSolution := solutionErrors_eq_empty.mp solutionEmpty
      statementTarget := targetErrors_eq_empty.mp targetEmpty
      programRooted := programErrors_eq_empty.mp programEmpty
      importsOnlySpecs := importErrors_eq_empty.mp importEmpty
      closureHoldsNoCode := noCode_of_closureErrors closureEmpty importEmpty
      declaresOnlyTheoremsAndHoles := filledErrors_eq_empty.mp filledEmpty
      assumesNoAxiom := axiomErrors_eq_empty.mp axiomEmpty
      targetsPublic := privateErrors_eq_empty.mp privateEmpty
      namesPlain := plain_of_plainErrors plainEmpty privateEmpty
      auxiliariesPublic := auxiliaryErrors_eq_empty.mp auxiliaryEmpty
      headlinesMentionHoles := mentions
      headlinesKilled := killed
      killsNameHeadlines := kills.1
      killsReject := kills.2
      killsMarked := marked
      headlinesDistinct := duplicateErrors_eq_empty.mp duplicateEmpty
      holesMentioned := holeErrors_eq_empty.mp holeEmpty
      hypothesesClaimed := hypothesisErrors_eq_empty.mp hypothesisEmpty
      preconditionsWitnessed := witnesses.1
      witnessesDerived := witnesses.2.1
      witnessesStated := witnesses.2.2
      foreignPreconditionsPremised := unprovableErrors_eq_empty.mp unprovableEmpty
      terminatesNamesHole := fun termination member => (terminations termination member).1
      terminatesOnKilledHeadline := fun termination member => (terminations termination member).2.1
      terminatesMentionsHole := fun termination member => (terminations termination member).2.2
      ownedAdmitted := ownedViolationErrors_eq_empty.mp ownedViolationEmpty
      specImportsOwned := specImportErrors_eq_empty.mp specImportEmpty
      ownedClaimsDeclared := ownedClaimErrors_eq_empty.mp ownedClaimEmpty
      ownedDerivedTotal := derivedPartialErrors_eq_empty.mp derivedEmpty
      ownedDigested := digestedOwned
      lockCurrent := current
      lintDriven := driven
      testDriven := tested
      builtinLintOff := unlinted }
  · intro complete
    refine ⟨⟨complete.lintDriven, complete.testDriven, complete.builtinLintOff⟩, ?_, ?_⟩
    · exact lockingErrors_eq_empty.mpr ⟨complete.ownedDigested, complete.lockCurrent⟩
    · simp only [findings, setupErrors, ownershipErrors, ownerErrors, meaningErrors, statedErrors,
        Array.append_eq_empty_iff, and_assoc]
      exact ⟨challengeErrors_eq_empty.mpr complete.challengeFound, solutionErrors_eq_empty.mpr complete.oneSolution,
        targetErrors_eq_empty.mpr complete.statementTarget, programErrors_eq_empty.mpr complete.programRooted,
        importErrors_eq_empty.mpr complete.importsOnlySpecs, closureErrors_eq_empty complete.closureHoldsNoCode,
        filledErrors_eq_empty.mpr complete.declaresOnlyTheoremsAndHoles,
        axiomErrors_eq_empty.mpr complete.assumesNoAxiom, privateErrors_eq_empty.mpr complete.targetsPublic,
        plainErrors_empty complete.namesPlain, ownedViolationErrors_eq_empty.mpr complete.ownedAdmitted,
        specImportErrors_eq_empty.mpr complete.specImportsOwned,
        ownedClaimErrors_eq_empty.mpr complete.ownedClaimsDeclared,
        derivedPartialErrors_eq_empty.mpr complete.ownedDerivedTotal,
        duplicateErrors_eq_empty.mpr complete.headlinesDistinct,
        mentionErrors_empty complete.headlinesMentionHoles, unmarkedErrors_empty complete.killsMarked,
        noKillErrors_empty complete.headlinesKilled, killErrors_empty complete.killsNameHeadlines complete.killsReject,
        witnessErrors_empty complete.preconditionsWitnessed complete.witnessesDerived complete.witnessesStated,
        holeErrors_eq_empty.mpr complete.holesMentioned,
        terminationErrors_eq_empty.mpr fun termination member =>
          ⟨complete.terminatesNamesHole termination member, complete.terminatesOnKilledHeadline termination member,
            complete.terminatesMentionsHole termination member⟩,
        hypothesisErrors_eq_empty.mpr complete.hypothesesClaimed,
        unprovableErrors_eq_empty.mpr complete.foreignPreconditionsPremised,
        auxiliaryErrors_eq_empty.mpr complete.auxiliariesPublic⟩

theorem run_code_eq_zero {lake : LakeFacts} {files : FileFacts} {challenge : ChallengeFacts} :
    (run lake files challenge).code = 0 ↔ setupOf lake = #[] ∧ errors lake files challenge = #[] := by
  unfold run
  by_cases unset : setupOf lake = #[]
  · by_cases empty : errors lake files challenge = #[]
    · simp [unset, empty]
    · simp [unset, isEmpty_eq_false empty, empty]
  · simp [isEmpty_eq_false unset, unset]

theorem run_setup {lake : LakeFacts} {files : FileFacts} {challenge : ChallengeFacts} :
    (run lake files challenge).setup = setupOf lake := by
  simp [run]

theorem run_errors {lake : LakeFacts} {files : FileFacts} {challenge : ChallengeFacts} :
    (run lake files challenge).errors = errors lake files challenge := by
  simp [run]

end Statement

theorem Statement.run_code_eq_zero_iff (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) :
    (Statement.run lake files challenge).code = 0 ↔ Statement.Complete lake files challenge := by
  rw [Statement.run_code_eq_zero, Statement.clean_iff_complete]

theorem Statement.run_code_ne_zero_iff (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) :
    (Statement.run lake files challenge).code ≠ 0 ↔
      (Statement.run lake files challenge).setup ≠ #[] ∨ (Statement.run lake files challenge).errors ≠ #[] := by
  rw [ne_eq, Statement.run_code_eq_zero, Statement.run_setup, Statement.run_errors]
  exact Classical.not_and_iff_not_or_not

private def acceptedLake : LakeFacts :=
  { packageDir := "", configFiles := #[], modules := #[⟨`Solution, "Solution.lean"⟩],
    challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩], defaultExeRoots := #[], packages := #[],
    defaultTargets := #[`statement], builtinLint := none, testDriver := "software_challenge/test_challenge", testDriverArgs := #[],
    testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, ownTests := #[], inputs := #[] }

private def acceptedFiles : FileFacts :=
  { lock := .missing, comparator := .missing, digests := #[⟨"Challenge.lean", "0"⟩, ⟨"Solution.lean", "1"⟩] }

private def acceptedChallenge : ChallengeFacts :=
  { module := `Challenge, file := "Challenge.lean", runtimeImports := #[], metaImports := #[], closure := #[],
    headlines := #[], kills := #[], witnesses := #[], holes := #[], filled := #[], axioms := #[], terminating := #[],
    replaceable := #[] }

private theorem accepted : Statement.Complete acceptedLake acceptedFiles acceptedChallenge where
  challengeFound := ⟨⟨`Challenge, "Challenge.lean"⟩, rfl, rfl⟩
  oneSolution := ⟨⟨`Solution, "Solution.lean"⟩, by simp [acceptedLake], rfl, fun other member _ => by
    simp [acceptedLake] at member
    simp [member]⟩
  statementTarget := by simp [acceptedLake]
  programRooted := fun nonempty => absurd rfl nonempty
  importsOnlySpecs := by simp [acceptedChallenge]
  closureHoldsNoCode := by simp [acceptedChallenge]
  declaresOnlyTheoremsAndHoles := rfl
  assumesNoAxiom := rfl
  targetsPublic := by simp [acceptedChallenge, ChallengeFacts.targets, ChallengeFacts.theorems]
  namesPlain := by simp [acceptedChallenge, ChallengeFacts.targets, ChallengeFacts.theorems]
  auxiliariesPublic := by simp [acceptedChallenge, ChallengeFacts.targets, ChallengeFacts.theorems]
  headlinesMentionHoles := by simp [acceptedChallenge]
  headlinesKilled := by simp [acceptedChallenge]
  killsNameHeadlines := by simp [acceptedChallenge]
  killsReject := by simp [acceptedChallenge]
  killsMarked := by simp [acceptedChallenge]
  headlinesDistinct := by simp [acceptedChallenge]
  holesMentioned := by simp [acceptedChallenge]
  hypothesesClaimed := by simp [acceptedChallenge]
  preconditionsWitnessed := by simp [acceptedChallenge]
  witnessesDerived := by simp [acceptedChallenge]
  witnessesStated := by simp [acceptedChallenge]
  foreignPreconditionsPremised := by simp [acceptedChallenge]
  terminatesNamesHole := by simp [acceptedChallenge]
  terminatesOnKilledHeadline := by simp [acceptedChallenge]
  terminatesMentionsHole := by simp [acceptedChallenge]
  ownedAdmitted := {
    placed := by simp [acceptedChallenge, Inventory.restrictedTo]
    modular := by simp [acceptedChallenge, Inventory.restrictedTo]
    layered := by simp [acceptedChallenge, Inventory.restrictedTo]
    pure := by simp [acceptedChallenge, Inventory.restrictedTo] }
  specImportsOwned := by simp [acceptedChallenge]
  ownedClaimsDeclared := by simp [acceptedChallenge]
  ownedDerivedTotal := by simp [acceptedChallenge]
  ownedDigested := fun path owned => by
    rcases owned with listed | named | ⟨source, listed, -, filed⟩
    · simp [acceptedLake] at listed
    · exact ⟨⟨"Challenge.lean", "0"⟩, by simp [acceptedFiles], named.symm⟩
    · simp [acceptedLake] at listed
      subst listed
      exact ⟨⟨"Solution.lean", "1"⟩, by simp [acceptedFiles], filed⟩
  lockCurrent := .inl rfl
  lintDriven := rfl
  builtinLintOff := rfl

theorem Statement.run_code_eq_zero_iff_rejects_accepting :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 0 } :
          Statement.Result)) lake files challenge).code = 0 ↔ Statement.Complete lake files challenge := by
  intro holds
  have complete := (holds { acceptedLake with defaultTargets := #[] } acceptedFiles acceptedChallenge).mp rfl
  simpa using complete.statementTarget

theorem Statement.run_code_eq_zero_iff_rejects_refusing :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
          Statement.Result)) lake files challenge).code = 0 ↔ Statement.Complete lake files challenge := by
  intro holds
  have refused := (holds acceptedLake acceptedFiles acceptedChallenge).mpr accepted
  simp at refused

theorem Statement.run_code_ne_zero_iff_rejects_accepting :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[.noStatementTarget], writes := { lock? := none, config? := none },
           code := 0 } : Statement.Result)) lake files challenge).code ≠ 0 ↔
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[.noStatementTarget], writes := { lock? := none, config? := none },
             code := 0 } : Statement.Result)) lake files challenge).setup ≠ #[] ∨
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[.noStatementTarget], writes := { lock? := none, config? := none },
             code := 0 } : Statement.Result)) lake files challenge).errors ≠ #[] := by
  intro holds
  have refused := (holds default default default).mpr (by simp)
  simp at refused

theorem Statement.run_code_ne_zero_iff_rejects_refusing :
    ¬ ∀ (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts),
      ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
        ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
          Statement.Result)) lake files challenge).code ≠ 0 ↔
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
            Statement.Result)) lake files challenge).setup ≠ #[] ∨
        ((fun (_ : LakeFacts) (_ : FileFacts) (_ : ChallengeFacts) =>
          ({ setup := #[], errors := #[], writes := { lock? := none, config? := none }, code := 1 } :
            Statement.Result)) lake files challenge).errors ≠ #[] := by
  intro holds
  have refused := (holds default default default).mp (by simp)
  simp at refused

end SoftwareChallenge

module

public import SoftwareChallenge.CoreCode.Rules.Standing
public import SoftwareChallenge.CoreCode.Rules.Follows
public import SoftwareChallenge.CoreCode.Report.Report
public import SoftwareChallenge.CoreCode.Layering
public import SoftwareChallenge.CoreCode.Format

public section

namespace SoftwareChallenge

open Lean

namespace Lint

def unauditedModules (facts : Facts) : Array Error :=
  facts.lake.modules.filterMap fun source =>
    if (source.module ≠ facts.challenge.module →
        ∃ fact ∈ facts.solution.inventory.modules, fact.name = source.module) then none
    else some (.unaudited source.module)

def unauditedExeRoots (facts : Facts) : Array Error :=
  facts.lake.exeRoots.filterMap fun root =>
    if ∃ fact ∈ facts.solution.inventory.modules, fact.name = root then none else some (.unaudited root)

def unlintedModules (facts : Facts) : Array Error :=
  facts.solution.inventory.modules.filterMap fun fact =>
    if fact.name ∈ facts.solution.linted then none else some (.unlinted fact.name)

def lintWarnings (facts : Facts) : Array Error :=
  facts.solution.lints.map .lintWarning

def sorries (facts : Facts) : Array Error :=
  facts.solution.sorries.map .sorryUsed

def explained (facts : Facts) : Violation → Array Error
  | .axioms declaration found =>
    let blamed := facts.solution.blames.filter (·.declaration == declaration)
    if blamed.isEmpty then #[.violation (.axioms declaration found)] else blamed.map .axiomUse
  | violation => #[.violation violation]

def violations (facts : Facts) : Array Error :=
  (facts.lake.project.violations facts.solution.inventory).flatMap (explained facts)

def editableMetaImports (facts : Facts) : Array Error :=
  facts.solution.inventory.modules.flatMap fun fact =>
    if (Role.ofName fact.name).Owned then
      fact.imports.filterMap fun dependency =>
        if (dependency.comptime = true → facts.lake.Builds dependency.name →
            facts.challenge.Owns dependency.name) then none
        else some (.metaImportsEditable fact.name dependency)
    else #[]

def firstModules (declarations : Array DeclarationFact) : Std.HashMap Name Name :=
  declarations.foldl (init := {}) fun first fact =>
    if first.contains fact.name then first else first.insert fact.name fact.module

def duplicates (facts : Facts) : Array Error :=
  let first := firstModules facts.solution.inventory.declarations
  facts.solution.inventory.declarations.filterMap fun fact =>
    match first[fact.name]? with
    | some module => if module = fact.module then none else some (.declaredTwice fact.name module fact.module)
    | none => none

def holesOutsideCode (facts : Facts) : Array Error :=
  facts.challenge.holes.flatMap fun hole => facts.solution.found.filterMap fun found =>
    if (found.constant.name = hole.constant.name →
        facts.lake.project.role? found.module = some .coreCode ∨
          facts.lake.project.role? found.module = some .worldCode) then none
    else some (.holeOutsideCode hole.constant.name found.module)

def noncomputableHoles (facts : Facts) : Array Error :=
  facts.challenge.holes.flatMap fun hole => facts.solution.found.filterMap fun found =>
    if (found.constant.name = hole.constant.name → found.compiled = true) then none
    else some (.holeNoncomputable hole.constant.name found.module)

def mainOutsidePrograms (facts : Facts) : Array Error :=
  match facts.solution.main? with
  | some main =>
    if (facts.lake.Program → facts.lake.project.role? main.1 = some .worldCode) then #[]
    else #[.mainOutsideProgram main.1]
  | none => #[]

def notFixpoints (facts : Facts) : Array Error :=
  facts.challenge.terminating.filterMap fun termination =>
    if ((∃ found ∈ facts.solution.found, found.constant.name = termination.definition) →
        termination.definition ∈ facts.solution.fixpoints) then none
    else some (.notFixpoint termination.definition termination.headline)

def fixpointsWithoutTerminates (facts : Facts) : Array Error :=
  facts.challenge.holes.filterMap fun hole =>
    if (hole.constant.name ∈ facts.solution.fixpoints →
        ∃ termination ∈ facts.challenge.terminating, termination.definition = hole.constant.name) then none
    else some (.fixpointWithoutTerminates hole.constant.name
      (((facts.solution.foundNamed? hole.constant.name).map (·.module)).getD .anonymous))

def misplacedClaims (facts : Facts) : Array Error :=
  facts.solution.registrations.filterMap fun registration =>
    if registration.home? ≠ some registration.module then some (.unregisteredClaim registration)
    else if facts.lake.project.role? registration.module ≠ some .worldSpec then
      some (.claimOutsideWorldSpec registration.claim registration.module)
    else none

def unreadableProofs (facts : Facts) : Array Error :=
  facts.challenge.headlines.flatMap fun headline => facts.solution.found.filterMap fun found =>
    if (found.constant.name = headline.target.constant.name → found.constant.kind = .proved →
        found.constant.value? ≠ none) then none
    else some (.proofUnreadable headline.target.constant.name found.module)

def ownedPaths (facts : Facts) : Array String :=
  facts.lake.configFiles.push facts.challenge.file ++
    (facts.lake.modules.filter fun source => decide (facts.challenge.Owns source.module)).map (·.file)

def unreadOwnedFiles (facts : Facts) : Array Error :=
  (ownedPaths facts).filterMap fun path => if facts.files.Digested path then none else some (.ownedUnread path)

def violationPath : Lock.Violation → String
  | .unrecorded path | .differs path | .missing path => path

def lockErrors (facts : Facts) : Array Error :=
  match facts.files.lock with
  | .missing => #[.lockMissing]
  | .unreadable problem => #[.lockUnreadable problem]
  | .decoded locked => (Lock.violations locked facts.files.digests).map fun violation =>
    .lock violation (ownedFile? facts (violationPath violation))

def configMatches (config : Config) (challenge : ChallengeFacts) (solution : Name) : Bool :=
  config.challenge == challenge.module && config.solution == solution &&
    config.theorems.all (fun name => challenge.theorems.any (·.constant.name == name)) &&
    challenge.theorems.all (config.theorems.contains ·.constant.name) &&
    config.definitions.all (fun name => challenge.holes.any (·.constant.name == name)) &&
    challenge.holes.all (config.definitions.contains ·.constant.name) &&
    config.axioms.all standardAxioms.contains && standardAxioms.all config.axioms.contains

def staleness (facts : Facts) (config : Config) : Error :=
  let declared := facts.challenge.theorems.map (·.constant.name) ++ facts.challenge.holes.map (·.constant.name)
  let listed := config.theorems ++ config.definitions
  let expected := solutionModules facts
  .comparatorStale (listed.filter (!declared.contains ·)) (declared.filter (!listed.contains ·)) (some config.solution)
    (if expected.size = 1 then expected[0]? else none)

def comparatorErrors (facts : Facts) : Array Error :=
  match facts.files.comparator with
  | .missing => #[.comparatorMissing]
  | .unreadable problem => #[.comparatorUnreadable problem]
  | .decoded config =>
    if facts.lake.modules.any fun source =>
        decide (Name.NamedSolution source.module) && configMatches config facts.challenge source.module then #[]
    else #[staleness facts config]

def solutionErrors (facts : Facts) : Array Error :=
  if facts.lake.OneSolution then #[] else #[.solutionModule (solutionModules facts)]

def targetErrors (facts : Facts) : Array Error :=
  if `statement ∈ facts.lake.defaultTargets then #[] else #[.noStatementTarget]

def challengeImports (facts : Facts) : Array Error :=
  facts.solution.imports.filterMap fun line =>
    if line.fact.name ≠ facts.challenge.module then none else some (.importsChallenge line)

def builtinLintErrors (facts : Facts) : Array Error :=
  match facts.lake.builtinLint with
  | some place => #[.builtinLintOn place]
  | none => #[]

def errorsOf (facts : Facts) : Array Error :=
  unauditedModules facts ++ unauditedExeRoots facts ++ violations facts ++ duplicates facts ++
    holesOutsideCode facts ++ noncomputableHoles facts ++ fixpointsWithoutTerminates facts ++ notFixpoints facts ++
    mainOutsidePrograms facts ++ misplacedClaims facts ++ unreadableProofs facts ++ editableMetaImports facts ++
    sorries facts ++ unlintedModules facts ++ lintWarnings facts ++ builtinLintErrors facts ++
    challengeImports facts ++ solutionErrors facts ++ targetErrors facts ++ unreadOwnedFiles facts ++
    lockErrors facts ++ comparatorErrors facts

def drifted (facts : Facts) : Bool :=
  match facts.files.lock with
  | .missing => false
  | _ => !(lockErrors facts).isEmpty

def mergeReasons (known added : List Reason) : List Reason :=
  known ++ added.filter (!known.contains ·)

def impureOf? : Error → Option Name
  | .violation (.impure declaration _ _) => some declaration
  | _ => none

def addReasons (added : List Reason) : Error → Error
  | .violation (.impure written role known) => .violation (.impure written role (mergeReasons known added))
  | other => other

def groupImpure (facts : Facts) (errors : Array Error) : Array Error :=
  errors.foldl (init := #[]) fun kept error => match error with
    | .violation (.impure declaration role reasons) =>
      let anchor := anchorOf facts ((moduleOf? facts declaration).getD .anonymous) declaration
      match kept.findIdx? (impureOf? · == some anchor) with
      | some index => kept.modify index (addReasons reasons)
      | none => kept.push (.violation (.impure anchor role reasons))
    | other => kept.push other

def impurePlace? (facts : Facts) : Error → Option (Name × Place)
  | .violation (.impure declaration _ _) =>
    some (declaration, declarationPlace facts ((moduleOf? facts declaration).getD .anonymous) declaration)
  | _ => none

def sorryPlace? (facts : Facts) (error : Error) : Option Place :=
  match error with
  | .violation (.axioms _ found) => if found[0]? == some ``sorryAx then some (error.message facts).place else none
  | .axiomUse blame => if blame.axiomName == ``sorryAx then some (error.message facts).place else none
  | _ => none

structure Pruning where
  modules : Std.HashMap Name Name
  targets : Std.HashSet Name
  named : Array Place
  twice : Std.HashSet Name
  noTarget : Bool
  drifted : Bool

def pruning (facts : Facts) (errors : Array Error) : Pruning :=
  { modules := facts.solution.inventory.declarations.foldl (init := {}) fun modules fact =>
      if modules.contains fact.name then modules else modules.insert fact.name fact.module
    targets := facts.challenge.targets.foldl (init := {}) fun targets target => targets.insert target.constant.name
    named := errors.filterMap fun error => (impurePlace? facts error).bind fun (declaration, place) =>
      if declaration.hasMacroScopes then none else some place
    twice := errors.foldl (init := {}) fun twice error => match error with
      | .declaredTwice name _ _ => twice.insert name
      | _ => twice
    noTarget := errors.any (· matches .noStatementTarget)
    drifted := drifted facts }

def Pruning.covers (pruning : Pruning) (blame : AxiomBlame) : Bool :=
  if blame.axiomName == blame.declaration then (nativeTactic? blame.axiomName).isSome
  else shownName blame.culprit != shownName blame.declaration && pruning.modules.contains blame.culprit &&
    !pruning.targets.contains (shownName blame.declaration)

def Pruning.redundant (facts : Facts) (pruning : Pruning) : Error → Bool
  | .lockMissing => pruning.noTarget
  | .comparatorMissing => pruning.noTarget || pruning.drifted
  | .comparatorStale .. | .comparatorUnreadable _ => pruning.drifted
  | .axiomUse blame => pruning.covers blame
  | .declaredTwice name _ second =>
    let anchor := anchorOf facts second name
    anchor != name && pruning.twice.contains anchor
  | error => match impurePlace? facts error with
    | some (declaration, place) => declaration.hasMacroScopes && pruning.named.contains place
    | none => false

def withoutRepeatedSorries (facts : Facts) (errors : Array Error) : Array Error :=
  let reported := errors.filterMap (sorryPlace? facts)
  errors.filter fun error => match error with
    | .sorryUsed place => !reported.contains { place with line := max 1 place.line }
    | _ => true

def reported (facts : Facts) (errors : Array Error) : Array Error :=
  let grouped := groupImpure facts errors
  let pruning := pruning facts grouped
  let kept := withoutRepeatedSorries facts (grouped.filter (!pruning.redundant facts ·))
  if kept.isEmpty then errors else kept

def unproved (facts : Facts) (targets : Array TargetFact) : Array Pending :=
  targets.filterMap fun target =>
    if facts.solution.holds target then none
    else some (.standing target.constant.name (facts.solution.standingOf target))

def mainItems (facts : Facts) : Array Pending :=
  if facts.lake.Program then
    match facts.solution.main? with
    | none => #[.mainMissing]
    | some _ =>
      let reached := reachedFromMain facts.solution
      (facts.challenge.holes.filter fun hole =>
        facts.solution.holds hole && !reached.contains hole.constant.name).map (.unreachedHole ·.constant.name)
  else #[]

def undecidedChecks (facts : Facts) : Array Pending :=
  facts.solution.claimUses.flatMap fun use => use.checks.filterMap fun check =>
    if check.2 ≠ .undecided then none else some (.undecidedCheck use check.1)

def claimUseOf (facts : Facts) (headline : HeadlineFact) (index : Nat) : ClaimUse :=
  let name := headline.target.constant.name
  match facts.solution.claimUses.find? fun use => use.headline == name && use.binder == index with
  | some use => use
  | none =>
    let (claim, statement) := ((headline.claims.find? (·.1 == index)).map (·.2)).getD (.anonymous, "")
    { headline := name, binder := index, claim, statement, checks := #[] }

def uncheckedClaims (facts : Facts) : Array Pending :=
  facts.challenge.headlines.flatMap fun headline =>
    (Array.range headline.binders.length).filterMap fun index =>
      match headline.binders[index]? with
      | some binder =>
        if (binder.kind = .claim → ∃ use ∈ facts.solution.claimUses, use.headline = headline.target.constant.name ∧
            use.binder = index ∧ ∃ check ∈ use.checks, check.2 = .matched) then none
        else some (.uncheckedClaim (claimUseOf facts headline index))
      | none => none

def hiddenDependencies (facts : Facts) : Array Pending :=
  facts.lake.packages.filterMap fun package =>
    if package.Visible facts.lake.packageDir then none else some (.hiddenDependency package)

def pendingOf (facts : Facts) : Array Pending :=
  unproved facts (facts.challenge.headlines.map (·.target)) ++ unproved facts facts.challenge.holes ++
    unproved facts (facts.challenge.kills.map (·.target)) ++ unproved facts (facts.challenge.witnesses.map (·.target)) ++
    mainItems facts ++ undecidedChecks facts ++ uncheckedClaims facts ++ hiddenDependencies facts

def code (errors : Array Error) (pending : Array Pending) : UInt32 :=
  if !errors.isEmpty then 1 else if !pending.isEmpty then 2 else 0

end Lint

def Lint.run (facts : Facts) : Lint.Result :=
  let errors := Lint.reported facts (Lint.errorsOf facts)
  let pending := if Lint.drifted facts then #[] else Lint.pendingOf facts
  { errors, pending, report := Report.lint facts errors pending, code := Lint.code errors pending }

end SoftwareChallenge

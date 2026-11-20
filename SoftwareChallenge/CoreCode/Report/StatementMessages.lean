module

public import SoftwareChallenge.CoreCode.Report.Message
public import SoftwareChallenge.CoreCode.Report.LintMessages
public import SoftwareChallenge.CoreCode.Rules.Statement
public import SoftwareChallenge.CoreCode.Graph
import Lean.PrivateName

public section

namespace SoftwareChallenge.Statement

open Lean

def relock : String := "delete owned.lock if there is one"

def lakefile (lake : LakeFacts) : String :=
  (lake.configFiles.find? (·.startsWith "lakefile")).getD "lakefile.lean"

def atLine (file : String) (line : Nat) : Place := { file, line := max line 1 }

def target? (challenge : ChallengeFacts) (name : Name) : Option TargetFact :=
  challenge.targets.find? (·.constant.name == name)

def headline? (challenge : ChallengeFacts) (name : Name) : Option HeadlineFact :=
  challenge.headlines.find? (·.target.constant.name == name)

def placeIn (challenge : ChallengeFacts) (place : Place) : Place :=
  atLine (if place.file.isEmpty then challenge.file else place.file) place.line

def placeOf (challenge : ChallengeFacts) (name : Name) : Place :=
  match target? challenge name with
  | some target => placeIn challenge target.place
  | none => atLine challenge.file 1

def writtenOf (challenge : ChallengeFacts) (name : Name) : String :=
  match target? challenge name with
  | some target => if target.written.isEmpty then toString name else target.written
  | none => toString name

def within (challenge : ChallengeFacts) (name : Name) : String :=
  match target? challenge name with
  | some target =>
    if target.enclosingNamespace.isAnonymous then "" else s!", inside `namespace {target.enclosingNamespace}`"
  | none => ""

def shown (name : Name) : String :=
  toString (privateToUserName name)

def suffixed (challenge : ChallengeFacts) (name : Name) (suffix : String) : String :=
  let space := ((target? challenge name).map (·.enclosingNamespace)).getD .anonymous
  toString (((privateToUserName name).appendAfter suffix).replacePrefix space .anonymous)

def templateOf (challenge : ChallengeFacts) (name : Name) : String :=
  match headline? challenge name with
  | some headline => headline.killTemplate?.getD s!"¬ ({headline.target.rendered})"
  | none => s!"¬ {name}"

def holesOf (challenge : ChallengeFacts) (name : Name) : String :=
  let found := match headline? challenge name with
    | some headline => (headline.target.constant.type.constants.filter challenge.isReplaceable).eraseDups
    | none => []
  if found.isEmpty then "each hole and foreign function it mentions" else " and ".intercalate (found.map toString)

def candidates (challenge : ChallengeFacts) : String :=
  ", ".intercalate (challenge.headlines.toList.map (writtenOf challenge ·.target.constant.name))

def sourceFile (module : Name) : String :=
  "/".intercalate (module.components.map toString) ++ ".lean"

def fileOf (lake : LakeFacts) (module : Name) : String :=
  ((lake.modules.find? (·.module == module)).map (·.file)).getD (sourceFile module)

def roleSuffix : Option Role → String
  | some role => s!" ({role})"
  | none => ", outside the package"

def ownedReason (challenge : ChallengeFacts) : Option OwnedFile → String
  | some .lakefile => "it configures how the package builds and how lint judges it"
  | some .manifest => "it pins the dependencies that build and check the statement"
  | some .toolchain => "it fixes the Lean version that checks the statement"
  | some .challenge => "it states the challenge"
  | some (.specModule _) => "a component of its module name is CoreSpec or WorldSpec, so it is part of the statement"
  | some (.closureModule module) => s!"{challenge.file} imports {module}, so it is part of the statement"
  | none => "owned.lock records it as part of the statement"

def configuration : Option OwnedFile → Bool
  | some .lakefile | some .manifest | some .toolchain | some .challenge => true
  | _ => false

def editable (lake : LakeFacts) (challenge : ChallengeFacts) (changed : String) : String :=
  let files := (lake.modules.filter fun source => source.module != challenge.module && source.file != changed &&
    !ownsModule challenge source.module).map (·.file)
  if files.isEmpty then "the CoreCode and WorldCode modules" else ", ".intercalate files.toList

def restore (path : String) : String :=
  s!"git checkout $(git log -1 --format=%H -- owned.lock) -- {path}"

def lockLine (files : FileFacts) (path : String) : Nat :=
  match files.lock with
  | .decoded locked => ((locked.findIdx? (·.path == path)).map (· + 2)).getD 1
  | _ => 1

def recordStep (next : Next) : String :=
  if next == .build then "delete owned.lock" else "delete owned.lock and run `lake build`"

def lockMessage (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) (next : Next)
    (violation : Lock.Violation) (owned? : Option OwnedFile) : Message :=
  let reason := ownedReason challenge owned?
  match violation with
  | .unrecorded path =>
    if owned?.isNone then
      { place := atLine path 1
        what := s!"owned.lock does not record {path}, which LSC's facets list as an input although nothing owns it \
          (it is not the Lake configuration, {challenge.file}, a module {challenge.file} imports, or a CoreSpec or \
          WorldSpec module)"
        why := "so owned.lock does not match the files the audit reads"
        fix := s!"To record {path} in owned.lock, {recordStep next}; to stop the audit from reading it, remove it from \
          the inputs that the facets compute in LSC's lakefile.lean"
        next }
    else
      { place := atLine path 1
        what := s!"{path} is owned, because {reason}, but owned.lock does not record it"
        why := if configuration owned? then "so a change to it would go unreviewed"
          else "so it would change the statement unreviewed"
        fix := if configuration owned? then s!"To record it, {recordStep next}"
          else s!"Remove or rename {path}, or, to add it to the statement, {recordStep next}"
        next }
  | .differs path =>
    { place := atLine path 1
      what := s!"{path} differs from owned.lock"
      why := s!"but {reason}, which a solution must not change"
      fix := s!"Restore it with `{restore path}` and edit {editable lake challenge path} instead, or, to change the \
        statement, {recordStep next}"
      next }
  | .missing path =>
    { place := atLine "owned.lock" (lockLine files path)
      what := s!"{path} is recorded in owned.lock but missing"
      why := s!"and {reason}, which a solution must not change"
      fix := s!"Restore it with `{restore path}`, or, to drop it from the statement, {recordStep next}"
      next }

def lockUnreadableMessage (problem : String) (next : Next) : Message :=
  { place := atLine "owned.lock" 1
    what := s!"owned.lock cannot be read: {problem}"
    why := "so nothing can tell whether the owned files changed"
    fix := s!"Restore it with `git checkout -- owned.lock`, or, to record the current statement, {recordStep next}"
    next }

def ownedUnreadMessage (lake : LakeFacts) (challenge : ChallengeFacts) (path : String) (next : Next) : Message :=
  let owned? := ownedFile? lake challenge path
  { place := atLine path 1
    what := s!"{path} is owned, because {ownedReason challenge owned?}, yet it could not be read"
    why := "so owned.lock cannot record what the statement rests on"
    fix := match owned? with
      | some (.specModule _) | some (.closureModule _) =>
        s!"Restore it with `git checkout -- {path}`, or remove its module from the lean_lib that builds it in \
          {lakefile lake}, and {relock}"
      | some .lakefile | some .manifest | some .toolchain | some .challenge | none =>
        s!"Restore it with `git checkout -- {path}`, and {relock}"
    next }

def noStatementTargetMessage (lake : LakeFacts) (next : Next) : Message :=
  { place := atLine (lakefile lake) 1
    what := s!"{lakefile lake} has no `statement` default target"
    why := "so `lake build` neither records owned.lock nor writes comparator.json"
    fix := s!"Add ``@[default_target] target statement pkg : Unit := do return (← pkg.fetchFacetJob \
      `softwareChallengeStatement).map (fun _ => ())`` to {lakefile lake}, and {relock}"
    next }

def solutionModuleMessage (lake : LakeFacts) (found : Array Name) (next : Next) : Message :=
  match found.toList.eraseDups with
  | [] =>
    let module := (((lake.modules[0]?).map (·.module.getRoot)).getD `MyApp) ++ `Solution
    { place := atLine (lakefile lake) 1
      what := "the package builds no module named Solution"
      why := "so the comparator has no proofs to check"
      fix := s!"Create {sourceFile module}, proving the headlines, kills, and witnesses, add `{module}` to the roots \
        of the default lean_lib in {lakefile lake} if it is not there, and {relock}"
      next }
  | named@(first :: _) =>
    { place := atLine (fileOf lake first) 1
      what := s!"{", ".intercalate (named.map toString)} are all named Solution"
      why := "but the comparator checks one module"
      fix := "Rename all but the module that proves the headlines, kills, and witnesses"
      next }

def importsChallengeMessage (lake : LakeFacts) (challenge : ChallengeFacts) (importing : ImportLine)
    (next : Next) : Message :=
  let file := fileOf lake importing.module
  let such := ((lake.modules.find? (Role.ofName ·.module == .coreSpec)).map fun source =>
    s!", such as `public import {source.module}`").getD ""
  { place := atLine file importing.fact.line
    what := s!"{importing.module} imports {challenge.module}"
    why := "but the challenge's holes share names with the solution's definitions, so the solution cannot be \
      checked against it"
    fix := s!"Replace `{importing.text}` at {file}:{max importing.fact.line 1} with imports of the CoreSpec and \
      WorldSpec modules {importing.module} uses{such}"
    next }

def wroteComparator (config : Config) : String :=
  s!"Wrote comparator.json: {config.theorems.size} theorems and {config.definitions.size} definitions for \
    `lake comparator` to check against {config.solution}"

def recordedLock (entries : Array Lock.Entry) : String :=
  s!"Recorded owned.lock: {" ".intercalate (entries.toList.map (·.path))}"

def terminationPlace (challenge : ChallengeFacts) (headline definition : Name) : Place :=
  match challenge.terminating.find? fun termination =>
      termination.headline == headline && termination.definition == definition with
  | some termination => placeIn challenge termination.place
  | none => placeOf challenge headline

def listedPlace (challenge : ChallengeFacts) (listed : Array (Name × Place)) (name : Name) : Place :=
  match listed.find? (·.1 == name) with
  | some (_, place) => placeIn challenge place
  | none => placeOf challenge name

def reachingImport? (challenge : ChallengeFacts) (module : Name) : Option ImportLine :=
  let graph := Graph.ofEdges challenge.imports
  (challenge.runtimeImports ++ challenge.metaImports).find? fun line =>
    (graph.closure #[line.fact.name]).contains module

def ownerOnly (module : Name) : String :=
  s!"{module} is owned, so no edit to the editable files fixes it"

def ownedModuleOf (challenge : ChallengeFacts) (declaration : Name) : Name :=
  ((challenge.owned.inventory.declarations.find? (·.name == declaration)).map (·.module)).getD .anonymous

def ownedAnchor (lake : LakeFacts) (challenge : ChallengeFacts) (module declaration : Name) : Option DeclarationPlace :=
  let file := fileOf lake module
  let placed := fun (candidate : Name) => challenge.owned.places.find? fun found =>
    found.name == candidate && found.place.file == file
  placed (Lint.anchorIn challenge.owned.parents (placed · |>.isSome) declaration)

def ownedPlace (lake : LakeFacts) (challenge : ChallengeFacts) (module declaration : Name) : Place :=
  match ownedAnchor lake challenge module declaration with
  | some found => atLine found.place.file found.place.line
  | none => atLine (fileOf lake module) 1

def ownedShown (lake : LakeFacts) (challenge : ChallengeFacts) (module declaration : Name) : Name :=
  match ownedAnchor lake challenge module declaration with
  | some found => Lint.shownName found.name
  | none => Lint.shownName declaration

def ownedImportText (challenge : ChallengeFacts) (module : Name) (dependency : ImportFact) : String :=
  match challenge.owned.imports.find? fun line => line.module == module && line.fact.name == dependency.name with
  | some line => line.text
  | none => s!"{if dependency.comptime then "meta import" else "import"} {dependency.name}"

def ownedImportLine (challenge : ChallengeFacts) (module dependency : Name) : ImportFact :=
  ((challenge.owned.inventory.modules.find? (·.name == module)).bind fun fact =>
    fact.imports.find? (·.name == dependency)).getD { name := dependency, comptime := false, line := 1 }

def axiomFault (axiomName culprit : Name) (file : String) : String × String :=
  if axiomName == ``sorryAx then
    (s!"{culprit} uses `sorry`", s!"Replace each `sorry` in {culprit} with a proof or a definition in {file}")
  else match Lint.nativeTactic? axiomName with
    | some tactic =>
      let replacement := if tactic == `native_decide then "`decide`" else "a proof the kernel checks, such as `decide`"
      (s!"{culprit} is proved with `{tactic}`, which asserts the evaluated result as an axiom",
        s!"Replace `{tactic}` in {culprit}, in {file}, with {replacement}")
    | none => (s!"{culprit} depends on axiom {privateToUserName axiomName}",
        s!"Prove {culprit} without {privateToUserName axiomName} in {file}")

def ownedAxiomMessage (lake : LakeFacts) (challenge : ChallengeFacts) (declaration : Name) (found : Array Name) :
    Message :=
  let module := ownedModuleOf challenge declaration
  let place := ownedPlace lake challenge module declaration
  let shown := ownedShown lake challenge module declaration
  let blame := (challenge.owned.blames.find? (·.declaration == declaration)).getD
    { declaration, axiomName := (found[0]?).getD ``sorryAx, culprit := declaration, culpritModule? := some module }
  if blame.axiomName == blame.declaration then
    { place, what := s!"`axiom {shown}` asserts {shown} without proof"
      why := s!"but the comparator permits only {standardAxiomList}, and {ownerOnly module}"
      fix := s!"Delete `axiom {shown}` from {fileOf lake module}, and state it as a headline of {challenge.file} or as \
        a WorldClaim in a WorldSpec module, and {relock}"
      next := .build }
  else
    let culpritModule := blame.culpritModule?.getD module
    let culprit := ownedShown lake challenge culpritModule blame.culprit
    let (fault, fix) := axiomFault blame.axiomName culprit (fileOf lake culpritModule)
    { place, what := if culprit == shown then fault else s!"{shown} is not proved, because {fault}"
      why := s!"but the comparator permits only {standardAxiomList}, so the proof is not checked, and \
        {ownerOnly module}"
      fix := s!"{fix}, and {relock}"
      next := .build }

def ownedImpureMessage (lake : LakeFacts) (challenge : ChallengeFacts) (declaration : Name) (role : Role)
    (reasons : List Reason) : Message :=
  let module := ownedModuleOf challenge declaration
  let file := fileOf lake module
  let place := ownedPlace lake challenge module declaration
  let shown := ownedShown lake challenge module declaration
  if reasons.contains .initializer || Lint.isInitializer declaration then
    { place, what := s!"{shown} runs IO when the program starts, in {module} ({role})"
      why := s!"but {role} code {role.purity}, and {ownerOnly module}"
      fix := s!"Move it from {file} to a WorldCode module, and {relock}"
      next := .build }
  else
    { place, what := s!"{shown} uses {" and ".intercalate (reasons.map Reason.offence)} in {module} ({role})"
      why := s!"but {role} code {role.purity}, and {ownerOnly module}"
      fix := s!"{(" and ".intercalate (reasons.map (·.cure shown))).capitalize} in {file}, and {relock}"
      next := .build }

def ownedViolationMessage (lake : LakeFacts) (challenge : ChallengeFacts) : Violation → Message
  | .unplaced module =>
    { place := atLine (fileOf lake module) 1
      what := s!"no lean_lib of the package builds {module}"
      why := s!"so the statement step gives it no role and cannot check what it declares, and {ownerOnly module}"
      fix := s!"Build {module} from a lean_lib in {lakefile lake}, and {relock}"
      next := .build }
  | .legacy module =>
    { place := atLine (fileOf lake module) 1
      what := s!"{module} does not start with `module`"
      why := s!"so the statement step cannot tell what it exposes, and {ownerOnly module}"
      fix := s!"Add `module` as the first line of {fileOf lake module}, and {relock}"
      next := .build }
  | .forbiddenImport module dependency role =>
    let file := fileOf lake module
    let found := ownedImportLine challenge module dependency
    let line := max 1 found.line
    { place := atLine file line
      what := s!"{module} ({role}) imports {dependency}{roleSuffix (lake.project.role? dependency)}"
      why := s!"but {role} may import {role.allowedImports}, so that {role.importPurpose}, and {ownerOnly module}"
      fix := s!"Delete line {line}, `{ownedImportText challenge module found}`, from {file}, and {relock}"
      next := .build }
  | .axioms declaration found => ownedAxiomMessage lake challenge declaration found
  | .impure declaration role reasons => ownedImpureMessage lake challenge declaration role reasons

def Setup.message (lake : LakeFacts) : Setup → Message
  | .lintDriver found =>
    { place := atLine (lakefile lake) 1
      what := if found.isEmpty then s!"the package block of {lakefile lake} does not set `lintDriver`"
        else s!"the package block of {lakefile lake} sets `lintDriver := \"{found}\"`"
      why := "so `lake lint` does not run the audit, and a `sorry` or an unproved headline goes unreported"
      fix := s!"Set `lintDriver := \"{auditLintDriver}\"` in the package block of {lakefile lake}, and {relock}"
      next := .build }
  | .testDriver found =>
    { place := atLine (lakefile lake) 1
      what := if found.isEmpty then s!"the package block of {lakefile lake} does not set `testDriver`"
        else s!"the package block of {lakefile lake} sets `testDriver := \"{found}\"`"
      why := "so `lake test` does not run the Checks, and a world claim nothing tests goes unreported"
      fix := s!"Set `testDriver := \"{auditTestDriver}\"` in the package block of {lakefile lake}, and {relock}"
      next := .build }
  | .builtinLint place =>
    { place := atLine place.file place.line
      what := s!"the package block of {lakefile lake} sets `builtinLint := true`"
      why := s!"but `lake lint` already runs Lean's linters through {auditLintDriver}, so they would run twice"
      fix := s!"Remove that line from {lakefile lake}, and {relock}"
      next := .build }

def claimWritten (claim : Name) : String :=
  match claim with
  | .str _ last => last
  | other => toString other

def Error.message (lake : LakeFacts) (files : FileFacts) (challenge : ChallengeFacts) : Error → Message
  | .duplicate later earlier =>
    { place := placeOf challenge later
      what := s!"{later} states the same as {earlier} ({Message.cite (placeOf challenge earlier)}), up to binder \
        names"
      why := "so it claims nothing new"
      fix := s!"Remove {later} and its kills from {challenge.file}, and {relock}"
      next := .build }
  | .mentionsNothing headline =>
    { place := placeOf challenge headline
      what := s!"{headline} mentions no hole or foreign function"
      why := "so no implementation can make it false, and no kill can show that it rejects one"
      fix := s!"State {headline} about a hole, or move it to a CoreSpec module as a lemma, and {relock}"
      next := .build }
  | .noKill headline suggestion? =>
    let written := writtenOf challenge headline
    { place := placeOf challenge headline
      what := s!"{headline} has no kill"
      why := "so nothing shows that it rejects a wrong implementation"
      fix := s!"Add `@[kills {written}] theorem {suffixed challenge headline "_rejects"} : \
        {suggestion?.getD (templateOf challenge headline)} := by sorry` to {challenge.file}\
        {within challenge headline}, replace each `?wrong_…` in it with a wrong implementation of that hole, and \
        {relock}"
      next := .build }
  | .unmarkedKill headline kill =>
    { place := placeOf challenge kill
      what := s!"{kill} states a kill of {headline} ({Message.cite (placeOf challenge headline)}) but is not marked \
        `@[kills {writtenOf challenge headline}]`"
      why := s!"so it counts as a headline to prove, not as a kill of {headline}"
      fix := s!"Mark {kill} `@[kills {writtenOf challenge headline}]` in {challenge.file}, and {relock}"
      next := .build }
  | .killOfNonHeadline kill named =>
    { place := placeOf challenge kill
      what := s!"{kill} is marked `@[kills {named}]`, but {named} is not a headline of {challenge.file}"
      why := "so the kill rejects nothing claimed"
      fix := if challenge.headlines.isEmpty then s!"Delete {kill} from {challenge.file}, and {relock}"
        else s!"Name in `@[kills …]` the headline it rejects, one of {candidates challenge}, or delete {kill} from \
          {challenge.file}, and {relock}"
      next := .build }
  | .killReplacesNothing kill headline =>
    { place := placeOf challenge kill
      what := s!"{kill} is `¬` {headline} with no hole replaced"
      why := s!"so it says that {headline} is false and can never be proved"
      fix := s!"Replace {holesOf challenge headline} in {kill} with a wrong implementation, and {relock}"
      next := .build }
  | .misshapenKill kill headline =>
    { place := placeOf challenge kill
      what := s!"{kill} is marked `@[kills {writtenOf challenge headline}]`, but it is neither `¬` {headline} with \
        its holes and foreign functions replaced by closed wrong implementations, nor that negation `∧` every other \
        headline in {challenge.file} order under the same replacement"
      why := s!"so it does not show that {headline} rejects anything"
      fix := s!"Restate {kill} as `{templateOf challenge headline}`, with each `?wrong_…` replaced by a wrong \
        implementation of that hole, or name in `@[kills …]` the headline it rejects, and {relock}"
      next := .build }
  | .unmentionedHole hole =>
    { place := placeOf challenge hole
      what := s!"no headline mentions hole {hole}"
      why := "so nothing is claimed about it"
      fix := s!"State a headline about {hole} in {challenge.file}, or remove the hole, and {relock}"
      next := .build }
  | .challengeImport line role? =>
    { place := atLine challenge.file line.fact.line
      what := s!"{challenge.module} imports {line.fact.name}{roleSuffix role?}"
      why := "but a challenge may import at runtime only CoreSpec and WorldSpec modules and modules outside the \
        package, so that the statement rests only on owned files"
      fix := s!"Delete line {max line.fact.line 1}, `{line.text}`, from {challenge.file}, import the CoreSpec or \
        WorldSpec modules it needs instead, and {relock}"
      next := .build }
  | .filled name =>
    { place := listedPlace challenge challenge.filled name
      what := s!"{challenge.module} defines {name} with a body"
      why := "but a challenge declares only theorems and holes, which the solution implements"
      fix := s!"Make {name} a hole with `:= sorry`, or move it to a CoreSpec module, and {relock}"
      next := .build }
  | .challengeAxiom name =>
    { place := listedPlace challenge challenge.axioms name
      what := s!"`axiom {name}` asserts {name} without proof"
      why := "but a challenge declares only theorems and holes, and the comparator permits no axiom of the challenge"
      fix := s!"Replace `axiom {name}` with a headline to prove, or with a WorldClaim in a WorldSpec module if it is \
        an assumption about the world, and {relock}"
      next := .build }
  | .privateTarget name =>
    let place := placeOf challenge name
    { place
      what := s!"{shown name} is `private`"
      why := "so the comparator and the audit cannot see it, and nothing claims it"
      fix := s!"Remove `private` from {shown name} at {Message.cite place}, and {relock}"
      next := .build }
  | .terminatesNotHole headline definition =>
    { place := terminationPlace challenge headline definition
      what := s!"`@[terminates {definition}]` on {headline} names {definition}, which is not a hole of \
        {challenge.file}"
      why := "so no headline speaks about its termination"
      fix := s!"Name a hole declared with `:= sorry` in {challenge.file}, or remove the attribute, and {relock}"
      next := .build }
  | .terminatesWithoutKill headline definition =>
    { place := terminationPlace challenge headline definition
      what := s!"`@[terminates {definition}]` is on {headline}, which is not a headline with a kill"
      why := "so nothing shows that it rejects a diverging implementation"
      fix := s!"Move the attribute to a headline with a kill, and {relock}"
      next := .build }
  | .terminatesUnmentioned headline definition =>
    { place := terminationPlace challenge headline definition
      what := s!"`@[terminates {definition}]` is on {headline}, which does not mention {definition}"
      why := s!"so it cannot state on which inputs {definition} returns"
      fix := s!"Move the attribute to a headline that mentions {definition}, and {relock}"
      next := .build }
  | .unnamedHypothesis headline hypothesis =>
    let shownHypothesis := s!"`{hypothesis.shown}`"
    if hypothesis.meaning.constants.any challenge.isReplaceable then
      { place := placeOf challenge headline
        what := s!"{headline} assumes {shownHypothesis}, which mentions a hole or foreign function and no input"
        why := s!"so the solution decides whether it holds, and when it does not, {headline} holds vacuously"
        fix := s!"Remove {shownHypothesis} from {headline}, or state it as its own headline with a kill, and {relock}"
        next := .build }
    else
      { place := placeOf challenge headline
        what := s!"{headline} assumes {shownHypothesis}, which is not a WorldClaim"
        why := s!"so no Check tests it, and a false assumption would make {headline} vacuous"
        fix := s!"Declare it in a WorldSpec module as `WorldClaim Name := {hypothesis.shown}`, with a doc comment, and \
          assume that instead, or remove it from {headline}, and {relock}"
        next := .build }
  | .privateAuxiliary headline auxiliary =>
    { place := placeOf challenge headline
      what := s!"the statement of {headline} elaborates to the private constant {shown auxiliary}"
      why := s!"which no solution can reproduce, so {headline} can never be proved"
      fix := s!"Write that part of the statement of {headline} as a term, without tactics or `decide`, and {relock}"
      next := .build }
  | .codeInClosure module =>
    let direct := (challenge.runtimeImports ++ challenge.metaImports).find? (·.fact.name == module)
    let reaching := direct.orElse fun _ => reachingImport? challenge module
    { place := atLine challenge.file ((reaching.map (·.fact.line)).getD 1)
      what := s!"{challenge.module} reaches {module} ({Role.ofName module}) through its imports\
        {match reaching with
          | some line => if direct.isSome then "" else s!", from line {max line.fact.line 1}, `{line.text}`"
          | none => ""}"
      why := "but code in the statement's import closure lets a solution change the statement by editing that code"
      fix := (match direct, reaching with
        | some line, _ => s!"Delete line {max line.fact.line 1}, `{line.text}`, from {challenge.file}, and {relock}"
        | none, some line => s!"Delete line {max line.fact.line 1}, `{line.text}`, from {challenge.file} and import \
            the CoreSpec or WorldSpec modules the statement needs instead, or move what the statement uses from \
            {module} into a CoreSpec module, and {relock}"
        | none, none => s!"Move what the statement uses from {module} into a CoreSpec module, and {relock}")
      next := .build }
  | .ownedViolation violation => ownedViolationMessage lake challenge violation
  | .specImport module dependency =>
    let file := fileOf lake module
    let line := max 1 dependency.line
    let role := Role.ofName module
    { place := atLine file line
      what := s!"{module} ({role}) {if dependency.comptime then "meta-imports" else "imports"} {dependency.name}\
        {roleSuffix (lake.project.role? dependency.name)}, which is not owned"
      why := s!"but {role} may import only owned modules, with `meta import` too, so that the statement rests only on \
        owned files: a solution may edit {dependency.name}, and with it the statement, while owned.lock stays the \
        same, and {ownerOnly module}"
      fix := s!"Move what {module} uses from {dependency.name} into a CoreSpec module and delete line {line}, \
        `{ownedImportText challenge module dependency}`, from {file}, and {relock}"
      next := .build }
  | .ownedClaim registration =>
    let file := fileOf lake registration.module
    if registration.home? != some registration.module then
      { place := atLine file registration.place.line
        what := s!"{registration.module} adds {registration.claim} to the world claims without the `WorldClaim` command"
        why := s!"so headlines could assume it as a checked claim, and {ownerOnly registration.module}"
        fix := s!"Delete the command in {file} that calls `SoftwareChallenge.claimsExt.addEntry`, and {relock}"
        next := .build }
    else
      { place := atLine file registration.place.line
        what := s!"WorldClaim {registration.claim} is declared in {registration.module}\
          {roleSuffix (lake.project.role? registration.module)}"
        why := s!"but a world claim is an assumption about the world, which only a WorldSpec module states, and \
          {ownerOnly registration.module}"
        fix := s!"Move the `WorldClaim {claimWritten registration.claim}` command and its doc comment from {file} to a \
          WorldSpec module, and {relock}"
        next := .build }
  | .derivedPartial declaration module =>
    { place := ownedPlace lake challenge module declaration
      what := s!"`deriving` makes {ownedShown lake challenge module declaration} a `partial` definition in {module} \
        ({Role.ofName module})"
      why := s!"so no proof can unfold it, and a statement that uses it cannot be proved about the code, and \
        {ownerOnly module}"
      fix := s!"Write that instance by structural recursion in {fileOf lake module}, or remove the `deriving` clause, \
        and {relock}"
      next := .build }
  | .witnessMissing headline =>
    let witness := suffixed challenge headline "_applies"
    { place := placeOf challenge headline
      what := s!"{headline} has a precondition or input that mentions a hole or foreign function, but its kills \
        derived no {witness}"
      why := s!"so nothing shows that some input meets its preconditions and the world claims about that input, and \
        {headline} could hold vacuously"
      fix := s!"State each precondition of {headline} as a hypothesis of its own in {challenge.file}, so that \
        `@[kills {writtenOf challenge headline}]` derives {witness}, and {relock}"
      next := .build }
  | .witnessPredeclared witness headline =>
    { place := placeOf challenge witness
      what := s!"{witness} is stated in {challenge.file}"
      why := s!"but `@[kills {writtenOf challenge headline}]` derives it from the preconditions and world claims of \
        {headline}, so a stated one may not be the witness they call for"
      fix := s!"Delete theorem {witness} from {challenge.file}, or rename it if it is a headline of its own, and \
        {relock}"
      next := .build }
  | .witnessMisstated witness headline =>
    { place := placeOf challenge witness
      what := s!"{witness}, which `@[kills {writtenOf challenge headline}]` derived, does not state the witness that \
        the binders of {headline} call for"
      why := s!"so it may not show that some input meets the preconditions of {headline} and the world claims about \
        that input, and no edit to the editable files can fix that, because software_challenge's witness derivation \
        wrote it"
      fix := s!"Update software_challenge in {lakefile lake} to a version whose derivation agrees with its \
        specification, and {relock}"
      next := .build }
  | .witnessUnprovable headline precondition foreign claim =>
    let witness := suffixed challenge headline "_applies"
    let telescope := ((headline? challenge headline).map (·.telescope)).getD []
    let shownAt := fun (index : Nat) => ((telescope[index]?).map (·.shown)).getD s!"hypothesis {index + 1}"
    let law := ((headline? challenge headline).map (·.lawOver challenge claim)).getD (shownAt claim)
    { place := placeOf challenge headline
      what := s!"{headline} assumes `{shownAt precondition}`, which mentions the foreign function {foreign}, and \
        every world claim it assumes about {foreign}, such as `{shownAt claim}`, names an input"
      why := s!"so {witness} must prove `{shownAt claim}` and `{shownAt precondition}` for some input with nothing \
        known about {foreign}, which no proof can do"
      fix := s!"State the claim as a law about {foreign} that names no input, such as `{law}`, which becomes a premise \
        of {witness}, or state `{shownAt precondition}` over what `{shownAt claim}` means, without {foreign}, in \
        {challenge.file}, and {relock}"
      next := .build }
  | .unplainName name =>
    let place := placeOf challenge name
    { place
      what := s!"{shown name} is not a plain name: a component of it is empty, starts with a digit, or holds `.`, a \
        quote, a backslash, `«`, `»`, or a control character"
      why := "so comparator.json cannot name it in a form that Lake reads back"
      fix := s!"Rename {writtenOf challenge name} at {Message.cite place} to an identifier that needs no `«»`, and \
        {relock}"
      next := .build }
  | .challengeLookup found =>
    if found.isEmpty then
      { place := atLine (lakefile lake) 1
        what := "no lean_lib of the package has a root module whose last component is Challenge"
        why := "so nothing states the challenge"
        fix := s!"Add ``lean_lib «Challenge» where leanOptions := #[⟨`warn.sorry, false⟩]`` to {lakefile lake}, \
          create Challenge.lean with the holes, the headlines, and a kill for each, and {relock}"
        next := .build }
    else
      { place := atLine (lakefile lake) 1
        what := s!"{", ".intercalate (found.toList.map fun source => s!"{source.module} ({source.file})")} are all \
          lean_lib roots whose last component is Challenge"
        why := "so the challenge is ambiguous"
        fix := s!"Rename all but the module that states the challenge, and {relock}"
        next := .build }
  | .challengeAbsent module file =>
    { place := atLine (lakefile lake) 1
      what := s!"{lakefile lake} names {module} as the challenge, but {file} was not read"
      why := "so nothing states the challenge"
      fix := s!"Create {file} with the holes, the headlines, and a kill for each, and {relock}"
      next := .build }
  | .challengeFails file =>
    { place := atLine file 1
      what := s!"{file} does not compile"
      why := "so its statements cannot be checked"
      fix := s!"Fix each error that Lean reports above for {file}, and {relock}"
      next := .build }
  | .solutionModule found => solutionModuleMessage lake found .build
  | .importsChallenge importing => importsChallengeMessage lake challenge importing .build
  | .noStatementTarget => noStatementTargetMessage lake .build
  | .exeRootsOutsideWorldCode roots =>
    let world := (lake.modules.find? (Role.ofName ·.module == .worldCode)).map (·.module)
    { place := atLine (lakefile lake) 1
      what := s!"no lean_exe of the package has a WorldCode root ({", ".intercalate (roots.toList.map toString)}), \
        though the package has WorldCode modules"
      why := "so the audit cannot tell which program runs the holes"
      fix := s!"In {lakefile lake}, set the `root` of the program's lean_exe to a WorldCode module\
        {(world.map fun module => s!", such as {module}").getD ""}, and {relock}"
      next := .build }
  | .ownedUnread path => ownedUnreadMessage lake challenge path .build
  | .lock violation owned? => lockMessage lake files challenge .build violation owned?
  | .lockUnreadable problem => lockUnreadableMessage problem .build

end SoftwareChallenge.Statement

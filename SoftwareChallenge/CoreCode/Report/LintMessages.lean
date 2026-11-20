module

public import SoftwareChallenge.CoreCode.Report.Message
public import SoftwareChallenge.CoreCode.Rules.Standing
public import SoftwareChallenge.CoreCode.Rules.Statement
public import Lean.PrivateName

public section

namespace SoftwareChallenge

open Lean

def standardAxiomList : String := "propext, Classical.choice, and Quot.sound"

def Role.allowedImports : Role → String
  | .coreSpec => "only CoreSpec modules and modules outside the package"
  | .worldSpec => "only CoreSpec and WorldSpec modules and modules outside the package"
  | .coreCode => "only CoreSpec and CoreCode modules and modules outside the package"
  | .worldCode => "any module except tooling"
  | .tooling => "any module"

def Role.importPurpose : Role → String
  | .coreSpec => "the statements rest only on pure definitions"
  | .worldSpec => "claims about the world rest only on the statements' definitions"
  | .coreCode => "pure code never reaches foreign code or effects"
  | .worldCode => "the program never runs tooling"
  | .tooling => "nothing constrains it"

def Role.purity : Role → String
  | .coreSpec | .coreCode => "must be pure and total, so that the proofs are about the code that runs"
  | .worldSpec => "may declare foreign code only as an `@[extern] opaque` that computes a value, so that the kernel \
      never unfolds it"
  | .worldCode => "may do IO but not use `unsafe`, `@[extern]`, or `@[implemented_by]`, so that the code that \
      runs is the code proved"
  | .tooling => "may do anything"

def Reason.offence : Reason → String
  | .«unsafe» => "`unsafe`"
  | .«partial» => "`partial`"
  | .extern => "`@[extern]`"
  | .implementedBy => "`@[implemented_by]`"
  | .initializer => "an initializer"
  | .io => "IO"
  | .debug => "a dbg builtin"
  | .unfoldableExtern => "`@[extern]` with a body the kernel unfolds"

def Reason.cure (reason : Reason) (name : Name) : String :=
  match reason with
  | .«unsafe» => s!"remove `unsafe` from {name}"
  | .«partial» => s!"remove `partial` from {name} and recurse structurally or with `termination_by`"
  | .extern => s!"remove `@[extern]` from {name}, since only a WorldSpec module declares foreign code, and only as \
      an `@[extern] opaque` that computes a value"
  | .implementedBy => s!"remove `@[implemented_by]` from {name}"
  | .initializer => s!"move the initializer of {name} to a WorldCode module"
  | .io => s!"move {name} to a WorldCode module"
  | .debug => s!"remove the `dbg_trace` or `dbgTraceIfShared` call from {name}"
  | .unfoldableExtern => s!"declare {name} as `@[extern \"…\"] opaque`, with no body"

def HeadlineFact.lawOver (headline : HeadlineFact) (challenge : ChallengeFacts) (claim : Nat) : String :=
  let binders := headline.binders challenge
  let named := (Telescope.close binders binders.length (((binders[claim]?).map (·.refers)).getD [])).filterMap
    fun index => (headline.telescope[index]?).map fun binder => s!"({binder.name} : {binder.shown})"
  let statement := ((headline.telescope[claim]?).map (·.shown)).getD ""
  if named.isEmpty then statement else s!"∀ {" ".intercalate named}, {statement}"

namespace Lint

def matchBudget : Nat := 200000

def statementTarget : String :=
  "@[default_target]\ntarget statement pkg : Unit := do\n  \
    return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())"

def ownerOf (name : Name) : Name :=
  let user := privateToUserName name
  let kept := (user.components.takeWhile (!·.isInternalOrNum)).foldl (· ++ ·) .anonymous
  let kept := if kept.isAnonymous then user else kept
  match privatePrefix? name with
  | some prefixName => prefixName ++ kept
  | none => kept

def shownName (name : Name) : Name := privateToUserName (ownerOf name)

def nativeTactic? (name : Name) : Option Name :=
  match (privateToUserName name).components.dropWhile (· != `_native) with
  | _ :: tactic :: _ => some tactic
  | _ => none

def isInitializer (name : Name) : Bool :=
  (privateToUserName name).components.contains `initFn

private def sourceFile (module : Name) : String :=
  "/".intercalate (module.components.map toString) ++ ".lean"

def fileOf (facts : Facts) (module : Name) : String :=
  if module == facts.challenge.module then facts.challenge.file
  else match facts.solution.inventory.modules.find? (·.name == module) with
    | some fact => fact.file
    | none => match facts.lake.modules.find? (·.module == module) with
      | some source => source.file
      | none => sourceFile module

private def lakefileOf (facts : Facts) : String :=
  (facts.lake.configFiles.find? fun file => file.endsWith "lakefile.lean" || file.endsWith "lakefile.toml").getD
    "lakefile.lean"

def moduleOf? (facts : Facts) (declaration : Name) : Option Name :=
  (facts.solution.inventory.declarations.find? (·.name == declaration)).map (·.module)

private def prefixes : Name → List Name
  | .anonymous => []
  | .str parent _ => parent :: prefixes parent
  | .num parent _ => parent :: prefixes parent

private def placeIn? (facts : Facts) (module name : Name) : Option DeclarationPlace :=
  if module.isAnonymous then facts.solution.places.find? (·.name == name)
  else
    let file := fileOf facts module
    facts.solution.places.find? fun found => found.name == name && found.place.file == file

def parentOf? (parents : Array (Name × Name)) (name : Name) : Option Name :=
  (parents.find? (·.1 == name)).map (·.2)

def settled (parents : Array (Name × Name)) (name : Name) : Name :=
  (List.range name.getNumParts).foldl (fun current _ => (parentOf? parents current).getD current) name

def anchorIn (parents : Array (Name × Name)) (placed : Name → Bool) (name : Name) : Name :=
  let written := settled parents (ownerOf (settled parents name))
  ((written :: prefixes written ++ [ownerOf name, name]).find? placed).getD name

def anchorOf (facts : Facts) (module name : Name) : Name :=
  anchorIn facts.solution.parents (fun candidate => (placeIn? facts module candidate).isSome) name

def declarationPlace (facts : Facts) (module name : Name) : Place :=
  match placeIn? facts module (anchorOf facts module name) with
  | some found => { found.place with line := max 1 found.place.line }
  | none => ⟨fileOf facts module, 1⟩

private def shownPlace (place : Place) : String := s!"{place.file}:{place.line}"

private def targetOf? (facts : Facts) (name : Name) : Option TargetFact :=
  facts.challenge.targets.find? (·.constant.name == name)

def hereOf (facts : Facts) (name : Name) : Place :=
  match targetOf? facts name with
  | some target => { target.place with line := max 1 target.place.line }
  | none => ⟨facts.challenge.file, 1⟩

private def isHole (facts : Facts) (name : Name) : Bool :=
  facts.challenge.holes.any (·.constant.name == name)

private def writtenOf (facts : Facts) (module name : Name) : String :=
  match targetOf? facts name with
  | some target => if target.written.isEmpty then toString name else target.written
  | none => match placeIn? facts module name with
    | some found => if found.written.isEmpty then toString (shownName name) else found.written
    | none => toString (shownName name)

private def within (space : Name) : String :=
  if space.isAnonymous then "" else s!", inside `namespace {space}`"

private def spaceOf (facts : Facts) (name : Name) : String :=
  within (((targetOf? facts name).map (·.enclosingNamespace)).getD .anonymous)

private def keywordOf (facts : Facts) (name : Name) : String :=
  if isHole facts name then "def" else "theorem"

private def signatureOf (facts : Facts) (name : Name) : String :=
  match targetOf? facts name with
  | some target =>
    let written := if target.written.isEmpty then toString name else target.written
    if target.signature.isEmpty then s!"{keywordOf facts name} {written} : {target.rendered}"
    else s!"{keywordOf facts name} {written} {target.signature}"
  | none => s!"{keywordOf facts name} {name}"

private def foreignClaimOf? (facts : Facts) (witness : Name) : Option (HeadlineFact × Nat × Name) := do
  let derived ← facts.challenge.witnesses.find? (·.target.constant.name == witness)
  let headline ← facts.challenge.headlines.find? (·.target.constant.name == derived.headline)
  (facts.challenge.replaceable.toList.filter (Statement.isForeignFunction facts.challenge)).findSome? fun foreign =>
    (Statement.unpremisedClaim? facts.challenge headline foreign).map (headline, ·, foreign)

private def purposeOf (facts : Facts) (name : Name) : String :=
  match facts.challenge.kills.find? (·.target.constant.name == name),
      facts.challenge.witnesses.find? (·.target.constant.name == name) with
  | some kill, _ => s!"so nothing shows that {kill.headline} rejects a wrong implementation"
  | _, some witness => s!"so nothing shows that some input meets the preconditions of {witness.headline} and the \
    world claims about that input"
  | none, none =>
    if isHole facts name then "so no headline about it can be proved" else "so the solution does not claim it yet"

private def roleOf? (facts : Facts) (module : Name) : Option Role :=
  facts.lake.project.role? module

private def located (facts : Facts) (module : Name) : String :=
  match roleOf? facts module with
  | some role => s!"{module} ({role})"
  | none => s!"{module}, outside the package"

private def filesIn (facts : Facts) (role : Role) : Array String :=
  (facts.lake.modules.filter (Role.ofName ·.module == role)).map (·.file)

private def codeFile (facts : Facts) : String :=
  ((filesIn facts .coreCode)[0]?).getD "a CoreCode module"

private def worldFile (facts : Facts) : String :=
  ((filesIn facts .worldCode)[0]?).getD "a WorldCode module"

def solutionModules (facts : Facts) : Array Name :=
  (facts.lake.modules.filter fun source => decide (Name.NamedSolution source.module)).map (·.module)

private def solutionName (facts : Facts) : Name :=
  match facts.solution.solution? with
  | some solution => solution
  | none => ((solutionModules facts)[0]?).getD `Solution

private def solutionFile (facts : Facts) : String :=
  fileOf facts (solutionName facts)

private def programFile? (facts : Facts) : Option String :=
  let worldRoots := facts.lake.defaultExeRoots.filter (Role.ofName · == .worldCode)
  let roots := if worldRoots.isEmpty then facts.lake.defaultExeRoots else worldRoots
  match roots with
  | #[root] => some (fileOf facts root)
  | _ => none

private def importOf? (facts : Facts) (module dependency : Name) : Option ImportFact :=
  (facts.solution.inventory.modules.find? (·.name == module)).bind fun fact =>
    fact.imports.find? (·.name == dependency)

private def importText (facts : Facts) (module dependency : Name) (comptime : Bool) : String :=
  match facts.solution.imports.find? fun line => line.module == module && line.fact.name == dependency with
  | some line => line.text
  | none => s!"{if comptime then "meta import" else "import"} {dependency}"

private def renamedInto (role : Role) (module : Name) : Name :=
  match module.components with
  | root :: rest@(_ :: _) => (root :: Name.mkSimple (toString role) :: rest).foldl (· ++ ·) .anonymous
  | _ => module ++ Name.mkSimple (toString role)

private def kindOf : ConstantKind → String
  | .assumed => "an axiom"
  | .defined .safe => "a def"
  | .defined .«unsafe» => "an unsafe def"
  | .defined .«partial» => "a partial def"
  | .proved => "a theorem"
  | .opaqueConstant => "an opaque constant, as `partial def` and `opaque` declare,"
  | .quotient => "a quotient primitive"
  | .inductiveType => "an inductive type"
  | .constructor => "a constructor"
  | .recursor => "a recursor"

def overridesFile : String := ".lake/package-overrides.json"

def ownedFile? (facts : Facts) (path : String) : Option OwnedFile :=
  if path.endsWith "lakefile.lean" || path.endsWith "lakefile.toml" then some .lakefile
  else if path.endsWith "lake-manifest.json" then some .manifest
  else if path.endsWith "lean-toolchain" then some .toolchain
  else if path == facts.challenge.file then some .challenge
  else (facts.lake.modules.find? (·.file == path)).bind fun source =>
    if decide (Role.ofName source.module).Owned then some (.specModule source.module)
    else if facts.challenge.closure.contains source.module then some (.closureModule source.module)
    else none

private def ownedReason (facts : Facts) : Option OwnedFile → String
  | some .lakefile => "it configures how the package builds and how lint judges it"
  | some .manifest => "it pins the dependencies that build and check the statement"
  | some .toolchain => "it fixes the Lean version that checks the statement"
  | some .challenge => "it states the challenge"
  | some (.specModule _) => "a component of its module name is CoreSpec or WorldSpec, so it is part of the statement"
  | some (.closureModule module) => s!"{facts.challenge.file} imports {module}, so it is part of the statement"
  | none => "it is part of the statement"

private def configures : Option OwnedFile → Bool
  | some .lakefile | some .manifest | some .toolchain | some .challenge => true
  | _ => false

private def restoreCommand (path : String) : String :=
  s!"git checkout $(git log -1 --format=%H -- owned.lock) -- {path}"

def editableFiles (facts : Facts) : Array String :=
  (facts.lake.modules.filter fun source =>
    source.module != facts.challenge.module && !decide (facts.challenge.Owns source.module)).map (·.file)

private def editableList (facts : Facts) : String :=
  match editableFiles facts with
  | #[] => "the CoreCode and WorldCode modules"
  | files => ", ".intercalate files.toList

def ownedList (facts : Facts) : Array String :=
  facts.lake.configFiles ++ #["owned.lock", facts.challenge.file] ++
    (facts.lake.modules.filter fun source =>
      source.module != facts.challenge.module && decide (facts.challenge.Owns source.module)).map (·.file)

def ownsModule (facts : Facts) (module : Name) : Bool :=
  module == facts.challenge.module || decide (facts.challenge.Owns module)

private def relock : String := "then delete owned.lock and run `lake build`"

private def ownerOnly (subject : String) : String := s!"{subject} is owned, so no edit to the editable files fixes it"

private def ownedModule? (facts : Facts) (module : Name) : Option String :=
  if ownsModule facts module then some (toString module) else none

private def ownedPath? (facts : Facts) (path : String) : Option String :=
  match ownedFile? facts path with
  | some (.specModule module) | some (.closureModule module) => some (toString module)
  | some .challenge => some (toString facts.challenge.module)
  | some _ => some path
  | none => none

private def withOwner (owner? : Option String) (message : Message) (ownerFix : String) : Message :=
  match owner? with
  | some owner => { message with why := s!"{message.why}, and {ownerOnly owner}", fix := s!"{ownerFix}, {relock}" }
  | none => message

private structure Fault where
  what : String
  why : String
  fix : String
  ownerFix : String

private def faultOf (axiomName culprit : Name) (nativePlace file : String) : Fault :=
  if axiomName == ``sorryAx then
    { what := s!"{culprit} uses `sorry`", why := "so it is not proved"
      fix := s!"Replace each `sorry` in {culprit} with a proof or a definition"
      ownerFix := s!"Replace each `sorry` in {culprit} with a proof or a definition in {file}" }
  else match nativeTactic? axiomName with
    | some tactic =>
      let replacement := if tactic == `native_decide then "`decide`" else "a proof the kernel checks, such as `decide`"
      let fix := s!"Replace `{tactic}` at {nativePlace} with {replacement}"
      { what := s!"{culprit} is proved with `{tactic}`, which asserts the evaluated result as an axiom"
        why := s!"but the comparator permits only {standardAxiomList}, so the proof is not checked", fix
        ownerFix := fix }
    | none =>
      let shown := privateToUserName axiomName
      { what := s!"{culprit} depends on axiom {shown}"
        why := s!"but the comparator permits only {standardAxiomList}, so its proof is not checked"
        fix := s!"Prove {culprit} without {shown}", ownerFix := s!"Prove {culprit} without {shown} in {file}" }

private def axiomWhose (axiomName : Name) : String :=
  if axiomName == ``sorryAx then "whose proof uses `sorry`"
  else match nativeTactic? axiomName with
    | some tactic => s!"which is proved with `{tactic}`, whose axiom the comparator does not permit"
    | none => s!"which depends on axiom {privateToUserName axiomName}"

private def blameMessage (facts : Facts) (blame : AxiomBlame) : Message :=
  let module := (moduleOf? facts blame.declaration).getD .anonymous
  let file := fileOf facts module
  let place := declarationPlace facts module blame.declaration
  let shown := shownName blame.declaration
  let owner? := ownedModule? facts module
  if blame.axiomName == blame.declaration then
    withOwner owner?
      { place, what := s!"`axiom {shown}` asserts {shown} without proof"
        why := s!"but the comparator permits only {standardAxiomList}"
        fix := s!"Delete `axiom {shown}` and prove what uses it", next := .lint }
      s!"Delete `axiom {shown}` from {file}, and state it as a headline of {facts.challenge.file} or as a WorldClaim \
        in a WorldSpec module"
  else
    let culprit := shownName blame.culprit
    let nativePlace := match moduleOf? facts blame.axiomName with
      | some axiomModule => shownPlace (declarationPlace facts axiomModule blame.axiomName)
      | none => shownPlace place
    if culprit == shown then
      let fault := faultOf blame.axiomName culprit nativePlace file
      withOwner owner? { place, what := fault.what, why := fault.why, fix := fault.fix, next := .lint } fault.ownerFix
    else match moduleOf? facts blame.culprit with
      | some culpritModule =>
        let fault := faultOf blame.axiomName culprit nativePlace (fileOf facts culpritModule)
        let what := s!"{shown} is not proved, because it uses {culprit} \
          ({shownPlace (declarationPlace facts culpritModule blame.culprit)})"
        match owner?, ownedModule? facts culpritModule with
        | none, some culpritOwner =>
          { place, what, why := s!"{axiomWhose blame.axiomName}, and {ownerOnly culpritOwner}"
            fix := s!"Prove {shown} without {culprit}", next := .lint }
        | _, culpritOwner? =>
          withOwner culpritOwner? { place, what, why := axiomWhose blame.axiomName, fix := fault.fix, next := .lint }
            fault.ownerFix
      | none =>
        let source := (blame.culpritModule?.map toString).getD "a module"
        withOwner owner?
          { place, what := s!"{shown} uses {culprit}, which {source} declares outside the package"
            why := s!"{axiomWhose blame.axiomName}, so the proof of {shown} is not checked"
            fix := s!"Prove {shown} without {culprit}", next := .lint }
          s!"Prove {shown} without {culprit} in {file}"

private def forbiddenImportMessage (facts : Facts) (module dependency : Name) (role : Role) : Message :=
  let file := fileOf facts module
  let found := importOf? facts module dependency
  let line := max 1 ((found.map (·.line)).getD 1)
  let comptime := (found.map (·.comptime)).getD false
  let text := importText facts module dependency comptime
  let message : Message :=
    { place := ⟨file, line⟩
      what := s!"{module} ({role}) {if comptime then "meta-imports" else "imports"} {located facts dependency}"
      why := s!"but {role} may import {role.allowedImports}, so that {role.importPurpose}"
      fix := s!"Delete line {line}, `{text}`, from {file}", next := .lint }
  match ownedModule? facts module with
  | some owner => withOwner (some owner) message message.fix
  | none =>
    if roleOf? facts dependency == some .tooling && (role == .coreCode || role == .worldCode) then
      let renamed := renamedInto .coreCode dependency
      let kinds := if role == .coreCode then "a CoreCode module" else "a CoreCode or WorldCode module"
      { message with
        fix := s!"Rename {dependency} to {kinds}, as in {renamed} ({sourceFile renamed}), and update line {line} of \
          {file}" }
    else message

private def impureMessage (facts : Facts) (declaration : Name) (role : Role) (reasons : List Reason) : Message :=
  let module := (moduleOf? facts declaration).getD .anonymous
  let file := fileOf facts module
  let anchor := anchorOf facts module declaration
  let place := declarationPlace facts module declaration
  let shown := shownName declaration
  let site := located facts module
  let owner? := ownedModule? facts module
  if reasons.contains .initializer || isInitializer declaration then
    let quoted := match placeIn? facts module anchor with
      | some found => if found.firstLine.isEmpty then s!"initialize {shown}" else found.firstLine
      | none => s!"initialize {shown}"
    let others := reasons.filter fun reason => reason != .initializer && reason != .io
    let also := if others.isEmpty then "" else s!", and {" and ".intercalate (others.map (·.cure shown))}"
    withOwner owner?
      { place, what := s!"`{quoted}` runs IO when the program starts, in {site}"
        why := s!"but {role} code {role.purity}"
        fix := s!"Move it to a WorldCode module{also}", next := .lint }
      s!"Move it from {file} to a WorldCode module{also}"
  else
    let fix := (" and ".intercalate (reasons.map (·.cure shown))).capitalize
    withOwner owner?
      { place, what := s!"{shown} uses {" and ".intercalate (reasons.map Reason.offence)} in {site}"
        why := s!"but {role} code {role.purity}", fix, next := .lint }
      s!"{fix} in {file}"

private def violationMessage (facts : Facts) : Violation → Message
  | .unplaced module =>
    let lakefile := lakefileOf facts
    { place := ⟨fileOf facts module, 1⟩, what := s!"no lean_lib of the package builds {module}"
      why := "so the audit gives it no role"
      fix := s!"Build it from a lean_lib in {lakefile}; {lakefile} is owned, so delete owned.lock and run \
        `lake build` to record it"
      next := .lint }
  | .legacy module =>
    let file := fileOf facts module
    let fix := s!"Add `module` as the first line of {file}"
    withOwner (ownedModule? facts module)
      { place := ⟨file, 1⟩, what := s!"{module} does not start with `module`"
        why := "so the audit cannot tell what it exposes", fix, next := .lint }
      fix
  | .forbiddenImport module dependency role => forbiddenImportMessage facts module dependency role
  | .axioms declaration found =>
    blameMessage facts { declaration, axiomName := (found[0]?).getD ``sorryAx, culprit := declaration
                         culpritModule? := moduleOf? facts declaration }
  | .impure declaration role reasons => impureMessage facts declaration role reasons

private def foundPlace (facts : Facts) (module name : Name) : Place :=
  match facts.solution.found.find? fun found => found.constant.name == name && found.module == module with
  | some found => { found.place with line := max 1 found.place.line }
  | none => declarationPlace facts module name

private def firstLineOf (text : String) : String :=
  (((text.splitOn "\n").map (·.trimAscii.toString)).find? (!·.isEmpty)).getD ""

private def difference (facts : Facts) (listedNotDeclared declaredNotListed : Array Name)
    (solutionListed? solutionExpected? : Option Name) : String :=
  let file := facts.challenge.file
  let names := fun (found : Array Name) => ", ".intercalate (found.map toString).toList
  let quoted := fun (module : Option Name) => match module with
    | some module => s!"\"{module}\""
    | none => "null"
  let parts := (if listedNotDeclared.isEmpty then [] else
      [s!"it lists {names listedNotDeclared}, which {file} no longer declares"]) ++
    (if declaredNotListed.isEmpty then [] else [s!"it omits {names declaredNotListed}, which {file} declares"]) ++
    if solutionListed? == solutionExpected? || solutionExpected?.isNone then [] else
      [s!"it names the solution module {quoted solutionListed?}, but the package's is {quoted solutionExpected?}"]
  if parts.isEmpty then "its contents differ from what `lake build` writes" else "; ".intercalate parts

def Error.message (facts : Facts) : Error → Message
  | .unaudited module =>
    if facts.lake.defaultExeRoots.contains module && !facts.lake.modules.any (·.module == module) then
      let lakefile := lakefileOf facts
      { place := ⟨lakefile, 1⟩, what := s!"{module} is the root of the package's lean_exe, but no default target builds it"
        why := "so the audit cannot see main or check what it may do"
        fix := s!"In {lakefile}, mark that lean_exe `@[default_target]`, or add {module} to the globs of the default \
          lean_lib; {lakefile} is owned, so then delete owned.lock and run `lake build`"
        next := .lint }
    else
      { place := ⟨fileOf facts module, 1⟩
        what := s!"lint read no compiled facts for {module}, which the default targets build"
        why := s!"so it cannot check what {module} imports and declares"
        fix := s!"Build {module} with `lake build {module}`, so that its compiled module exists", next := .lint }
  | .unlinted module =>
    { place := ⟨fileOf facts module, 1⟩, what := s!"lint has no record of Lean's linters for {module}"
      why := s!"so it cannot tell whether {module} passes them, which `lake lint` requires of every module the default \
        targets build"
      fix := s!"Build {module} with `lake build {module}`, so that its linter warnings are recorded", next := .lint }
  | .metaImportsEditable module dependency =>
    let file := fileOf facts module
    let line := max 1 dependency.line
    let role := Role.ofName module
    { place := ⟨file, line⟩, what := s!"{module} ({role}) meta-imports {located facts dependency.name}"
      why := s!"but {role} may import {role.allowedImports}, with `meta import` too, so that the statement rests only \
        on owned files: a solution may edit {dependency.name}, and with it the statement, while owned.lock stays the \
        same"
      fix := s!"Move what {module} uses from {dependency.name} into a CoreSpec module and delete line {line}, \
        `{importText facts module dependency.name true}`, from {file}; then delete owned.lock and run `lake build`"
      next := .lint }
  | .violation found => violationMessage facts found
  | .axiomUse blame => blameMessage facts blame
  | .holeOutsideCode hole module =>
    let fix := s!"Move `def {writtenOf facts module hole}` from {fileOf facts module} to {codeFile facts}, or to a \
      WorldCode module if it does IO{spaceOf facts hole}"
    withOwner (ownedModule? facts module)
      { place := foundPlace facts module hole, what := s!"hole {hole} is defined in {located facts module}"
        why := "but a hole is code, which lives in CoreCode or WorldCode, where the audit checks what it may do", fix
        next := .lint }
      fix
  | .holeNoncomputable hole module =>
    let fix := s!"Define {hole} without `noncomputable` in {fileOf facts module}"
    withOwner (ownedModule? facts module)
      { place := foundPlace facts module hole, what := s!"hole {hole} is `noncomputable` in {module}"
        why := "so no code runs it, and the headlines about it say nothing about a program", fix, next := .lint }
      fix
  | .fixpointWithoutTerminates hole module =>
    let fix := s!"Define {hole} by structural recursion or with `termination_by`, without `partial_fixpoint`, in \
      {fileOf facts module}"
    withOwner (ownedModule? facts module)
      { place := foundPlace facts module hole
        what := s!"hole {hole} is defined with `partial_fixpoint` in {module}, so it may not return, but no headline \
          of {facts.challenge.file} is marked `@[terminates {hole}]` to state on which inputs it does"
        why := s!"so a headline about {hole} could hold while the program never returns", fix, next := .lint }
      fix
  | .declaredTwice name first second =>
    let shown := shownName name
    let (edited, other) := if ownsModule facts second && !ownsModule facts first then (first, second)
      else (second, first)
    let fix := s!"Rename or delete {shown} in {fileOf facts edited}"
    withOwner (if ownsModule facts edited then some (toString edited) else none)
      { place := declarationPlace facts edited name
        what := s!"{shown} is declared in both {edited} and {other} ({shownPlace (declarationPlace facts other name)})"
        why := s!"and Lean keeps only the one it imports first, so the audit and the comparator never check the one \
          in {second}"
        fix, next := .lint }
      fix
  | .sorryUsed place =>
    let place := { place with line := max 1 place.line }
    match ownedPath? facts place.file with
    | some owner =>
      { place, what := "Lean reports `declaration uses 'sorry'` here"
        why := s!"so a proof or definition is missing, and {ownerOnly owner}"
        fix := s!"Replace each `sorry` at line {place.line} with a proof or a definition in {place.file}, {relock}"
        next := .lint }
    | none =>
      { place, what := "Lean reports `declaration uses 'sorry'` here"
        why := "so a proof or definition is missing, and the comparator rejects the solution"
        fix := s!"Replace each `sorry` at {shownPlace place} with a proof or a definition", next := .lint }
  | .mainOutsideProgram module =>
    let place := declarationPlace facts module `main
    let why := "but main runs the program, which does IO, and only WorldCode may"
    if facts.lake.defaultExeRoots.contains module then
      let lakefile := lakefileOf facts
      let moved := renamedInto .worldCode module
      { place, what := s!"main is defined in {located facts module}, the root of the package's lean_exe", why
        fix := s!"In {lakefile}, set that lean_exe's `root` to a WorldCode module, such as {moved}, and move \
          {fileOf facts module} to {sourceFile moved}; {lakefile} is owned, so then delete owned.lock and run \
          `lake build`"
        next := .lint }
    else
      let program := (programFile? facts).getD "the WorldCode module that is the root of the lean_exe"
      let fix := s!"Move `def main` from {fileOf facts module} to {program}, outside any namespace"
      withOwner (ownedModule? facts module)
        { place, what := s!"main is defined in {located facts module}", why, fix, next := .lint } fix
  | .notFixpoint hole headline =>
    let module := ((facts.solution.foundNamed? hole).map (·.module)).getD .anonymous
    let fix := s!"Define {hole} with `partial_fixpoint` after its body in {fileOf facts module}"
    withOwner (ownedModule? facts module)
      { place := foundPlace facts module hole, what := s!"hole {hole} is not defined with `partial_fixpoint`"
        why := s!"but `@[terminates {hole}]` on {headline} ({shownPlace (hereOf facts headline)}) admits it only as a \
          partial_fixpoint definition, whose termination {headline} states"
        fix, next := .lint }
      fix
  | .claimOutsideWorldSpec claim module =>
    let command := s!"the `WorldClaim {writtenOf facts module claim}` command and its doc comment"
    withOwner (ownedModule? facts module)
      { place := declarationPlace facts module claim
        what := s!"WorldClaim {claim} is declared in {located facts module}"
        why := "but a world claim is an assumption about the world, which only a WorldSpec module states"
        fix := s!"Remove {command} from {fileOf facts module}", next := .lint }
      s!"Move {command} from {fileOf facts module} to a WorldSpec module"
  | .unregisteredClaim registration =>
    let declared := match registration.home? with
      | some home => s!", declared at {shownPlace (declarationPlace facts home registration.claim)},"
      | none => ""
    let fix := s!"Delete the command in {fileOf facts registration.module} that calls \
      `SoftwareChallenge.claimsExt.addEntry`"
    withOwner (ownedModule? facts registration.module)
      { place := { registration.place with line := max 1 registration.place.line }
        what := s!"{registration.module} adds {registration.claim}{declared} to the world claims without the \
          `WorldClaim` command"
        why := "so headlines could assume it as a checked claim", fix, next := .lint }
      fix
  | .lintWarning lint =>
    let place := { lint.place with line := max 1 lint.place.line }
    let fix := s!"Change line {place.line} of {place.file} as the warning says"
    withOwner ((ownedModule? facts lint.module).orElse fun _ => ownedPath? facts place.file)
      { place, what := s!"Lean's linter {lint.linter} reports \"{firstLineOf lint.message}\""
        why := s!"so {lint.module} does not pass Lean's linters, which `lake lint` requires of every module the \
          default targets build"
        fix, next := .lint }
      fix
  | .ownedUnread path =>
    { place := ⟨path, 1⟩
      what := s!"{path} is owned, because {ownedReason facts (ownedFile? facts path)}, but lint could not read it"
      why := "so it cannot tell whether owned.lock records it as it is"
      fix := s!"Make {path} readable, or restore it with `{restoreCommand path}`", next := .lint }
  | .lock found owned? =>
    let reason := ownedReason facts owned?
    match found with
    | .unrecorded path =>
      if configures owned? then
        { place := ⟨path, 1⟩, what := s!"{path} is owned, because {reason}, but owned.lock does not record it"
          why := "so a change to it would go unreviewed"
          fix := "Delete owned.lock and run `lake build` to record it", next := .lint }
      else
        { place := ⟨path, 1⟩, what := s!"{path} is owned, because {reason}, but owned.lock does not record it"
          why := "so it would change the statement unreviewed"
          fix := s!"Remove or rename {path}; to add it to the statement, delete owned.lock and run `lake build` to \
            record it"
          next := .lint }
    | .differs path =>
      { place := ⟨path, 1⟩, what := s!"{path} differs from owned.lock"
        why := s!"but {reason}, which a solution must not change"
        fix := s!"Restore it with `{restoreCommand path}` and edit {editableList facts} instead; to change the \
          statement, delete owned.lock and run `lake build` to record it"
        next := .lint }
    | .missing path =>
      { place := ⟨path, 1⟩, what := s!"{path} is recorded in owned.lock but missing"
        why := s!"and {reason}, which a solution must not change"
        fix := s!"Restore it with `{restoreCommand path}`; to drop it from the statement, delete owned.lock and run \
          `lake build` to record it"
        next := .lint }
  | .lockMissing =>
    { place := ⟨"owned.lock", 1⟩, what := "owned.lock is missing"
      why := "so lint cannot check that the owned files are unchanged"
      fix := "Restore it with `git checkout -- owned.lock`, or run `lake build` to record the current statement"
      next := .lint }
  | .lockUnreadable problem =>
    { place := ⟨"owned.lock", 1⟩, what := s!"owned.lock cannot be read: {problem}"
      why := "so lint cannot check that the owned files are unchanged"
      fix := "Restore it with `git checkout -- owned.lock`, or delete owned.lock and run `lake build` to record the \
        current statement as `lake build` writes it"
      next := .lint }
  | .comparatorMissing =>
    { place := ⟨"comparator.json", 1⟩, what := "comparator.json is missing"
      why := s!"so `lake comparator` has nothing to check: `lake build` writes it from {facts.challenge.file}, and has \
        not written it here yet"
      fix := "Run `lake build`", next := .lint }
  | .comparatorStale listedNotDeclared declaredNotListed solutionListed? solutionExpected? =>
    { place := ⟨"comparator.json", 1⟩
      what := s!"comparator.json does not match {facts.challenge.file}: \
        {difference facts listedNotDeclared declaredNotListed solutionListed? solutionExpected?}"
      why := "so `lake comparator` would check another statement than the challenge's"
      fix := "Run `lake build` to regenerate it", next := .lint }
  | .comparatorUnreadable problem =>
    { place := ⟨"comparator.json", 1⟩, what := s!"comparator.json cannot be read: {problem}"
      why := "so `lake comparator` cannot check the solution"
      fix := "Delete comparator.json and run `lake build` to regenerate it", next := .lint }
  | .noStatementTarget =>
    let lakefile := lakefileOf facts
    { place := ⟨lakefile, 1⟩, what := s!"{lakefile} has no `statement` target"
      why := "so `lake build` neither records owned.lock nor writes comparator.json"
      fix := s!"Add these lines to {lakefile}, delete owned.lock if it exists, and run `lake build` to record \
        {lakefile} and write comparator.json\n\n{statementTarget}"
      next := .lint }
  | .solutionModule found =>
    let lakefile := lakefileOf facts
    let distinct := found.foldl (fun kept module => if kept.contains module then kept else kept.push module) #[]
    match distinct[0]? with
    | none =>
      let module := ((facts.lake.modules[0]?.map (·.module.getRoot)).getD `MyApp) ++ `Solution
      { place := ⟨lakefile, 1⟩, what := "the package builds no module named Solution"
        why := "so the comparator has no proofs to check"
        fix := s!"Create {sourceFile module}, proving the headlines, kills, and witnesses, and add `{module}` to the \
          roots of the default lean_lib in {lakefile} if it is not there; {lakefile} is owned, so then delete \
          owned.lock if it exists"
        next := .build }
    | some first =>
      { place := ⟨fileOf facts first, 1⟩
        what := s!"{", ".intercalate (distinct.map toString).toList} are all named Solution"
        why := "but the comparator checks one module"
        fix := "Rename all but the module that proves the headlines, kills, and witnesses", next := .build }
  | .importsChallenge importing =>
    let file := fileOf facts importing.module
    let line := max 1 importing.fact.line
    let spec := (facts.lake.modules.find? (Role.ofName ·.module == .coreSpec)).map (·.module)
    let message : Message :=
      { place := ⟨file, line⟩, what := s!"{importing.module} imports {facts.challenge.module}"
        why := "whose holes share names with the solution's definitions, so the solution cannot be checked against it"
        fix := s!"Replace `{importing.text}` at {file}:{line} with imports of the CoreSpec and WorldSpec modules \
          {importing.module} uses{(spec.map fun spec => s!", such as `public import {spec}`").getD ""}"
        next := .build }
    match ownedModule? facts importing.module with
    | some owner => { withOwner (some owner) message message.fix with next := .lint }
    | none => message
  | .builtinLintOn place =>
    let lakefile := lakefileOf facts
    { place := { place with line := max 1 place.line }, what := "the package block sets `builtinLint := true`"
      why := "but `lake lint` already runs Lean's linters through software_challenge/lint_challenge, so they would \
        run twice"
      fix := s!"Remove that line; {lakefile} is owned, so then delete owned.lock and run `lake build` to re-record it"
      next := .lint }
  | .proofUnreadable target module =>
    { place := foundPlace facts module target, what := s!"the proof of {target} in {module} cannot be read"
      why := "so lint cannot tell which world claims it uses or which headlines it follows from, as when a build \
        cache ships no .olean.private"
      fix := s!"Build {module} from its source with `lake build {module}`, without a downloaded cache, so that its \
        .olean.private exists"
      next := .lint }

private def claimBinder? (facts : Facts) (use : ClaimUse) : Option BinderFact :=
  (facts.challenge.headlines.find? (·.target.constant.name == use.headline)).bind fun headline =>
    headline.telescope[use.binder]?

private def claimShown (facts : Facts) (use : ClaimUse) : String :=
  match claimBinder? facts use with
  | some binder => if binder.shown.isEmpty then use.statement else binder.shown
  | none => use.statement

private def unprovableNote (facts : Facts) (name : Name) : String × String :=
  match foreignClaimOf? facts name with
  | some (headline, claim, foreign) =>
    let shown := ((headline.telescope[claim]?).map (·.shown)).getD ""
    (s!", and may have no proof: it conjoins `{shown}`, a world claim about what the opaque foreign function \
        {foreign} returns at a witnessed input, which a proof cannot establish",
      s!"; if no proof can show `{shown}`, state that claim in {facts.challenge.file} as a law about {foreign} that \
        names no input, such as `{headline.lawOver facts.challenge claim}`, which then becomes a premise of {name}, \
        {relock}")
  | none => ("", "")

def Pending.message (facts : Facts) : Pending → Message
  | .standing name current =>
    let here := hereOf facts name
    let hole := isHole facts name
    let what := if hole then s!"hole {name}" else toString name
    let space := spaceOf facts name
    match current with
    | .holds module =>
      { place := here, what := s!"lint lists {what} as pending though {module} proves it"
        why := "so the facts lint read disagree with each other"
        fix := s!"Build {module} again with `lake build {module}`", next := .lint }
    | .unsound module =>
      let (note, restated) := unprovableNote facts name
      { place := foundPlace facts module name, what := s!"{what} is proved in {module} with an axiom the comparator \
          does not permit{note}"
        why := "so its proof is not checked"
        fix := s!"Prove {name} with only {standardAxiomList}{restated}", next := .lint }
    | .absent =>
      if hole then
        { place := here, what := s!"hole {name} is not implemented yet", why := purposeOf facts name
          fix := s!"Add `{signatureOf facts name} := …` to {codeFile facts}, or to a WorldCode module if it does \
            IO{space}"
          next := .lint }
      else
        let (note, restated) := unprovableNote facts name
        { place := here, what := s!"{name} is not proved yet{note}", why := purposeOf facts name
          fix := s!"Add `{signatureOf facts name} := …`, with a proof, to {solutionFile facts}{space}{restated}"
          next := .lint }
    | .outside module importsSolution =>
      let file := fileOf facts module
      let solution := solutionName facts
      if importsSolution then
        { place := foundPlace facts module name, what := s!"{what} is in {module}, which imports {solution}"
          why := s!"so {solution} cannot import it back, and the comparator reads only {solution} and its imports"
          fix := s!"Move `{keywordOf facts name} {writtenOf facts module name}` from {file} into \
            {solutionFile facts}{space}"
          next := .lint }
      else
        { place := foundPlace facts module name, what := s!"{what} is in {module}, which {solution} does not import"
          why := s!"so the comparator, which reads only {solution} and its imports, cannot see it"
          fix := s!"Add `public import {module}` to the imports of {solutionFile facts}, or move {name} into \
            {solutionFile facts}"
          next := .lint }
    | .kind module found =>
      if hole then
        { place := foundPlace facts module name, what := s!"hole {name} is {kindOf found} in {module}"
          why := s!"but {shownPlace here} declares a `def`, so the comparator rejects it"
          fix := s!"Define it with `def`, without `partial`, `unsafe`, or `opaque`, in {fileOf facts module}"
          next := .lint }
      else
        { place := foundPlace facts module name, what := s!"{name} is {kindOf found} in {module}"
          why := s!"but {shownPlace here} states it as a theorem, so the comparator rejects it"
          fix := s!"Declare it with `theorem` in {fileOf facts module}", next := .lint }
    | .universes module found =>
      let shown := fun (levels : List Name) => if levels.isEmpty then "none" else ", ".intercalate (levels.map toString)
      let expected := ((targetOf? facts name).map (·.constant.levels)).getD []
      { place := foundPlace facts module name, what := s!"{what} has universe parameters {shown found} in {module}"
        why := s!"but {shown expected} in {shownPlace here}, so the comparator rejects it"
        fix := s!"Declare it with the universe parameters of {shownPlace here}, in that order", next := .lint }
    | .differs module plain explicit =>
      let (statedPlain, statedExplicit) := ((targetOf? facts name).map fun target =>
        (target.rendered, target.renderedExplicit)).getD ("", "")
      let (found, expected) := if plain == statedPlain then (explicit, statedExplicit) else (plain, statedPlain)
      { place := foundPlace facts module name
        what := s!"{what} {if hole then "has type" else "states"} `{found}` in {module}"
        why := s!"but `{expected}` in {shownPlace here}, so the comparator rejects it"
        fix := s!"Restate it as `{signatureOf facts name} := …`", next := .lint }
    | .auxiliary module constant =>
      { place := foundPlace facts module name
        what := s!"{what} elaborates to {constant} in {module}, which differs from the {constant} that \
          {shownPlace here} elaborates to"
        why := "so the comparator rejects it"
        fix := s!"Copy the statement of {name} from {shownPlace here} verbatim", next := .lint }
  | .mainMissing =>
    let holes := facts.challenge.holes.map (·.constant.name)
    let calls := if holes.isEmpty then "" else s!", calling {" and ".intercalate (holes.map toString).toList}"
    let why := "but the package declares a lean_exe, and the audit checks that main reaches every hole"
    match programFile? facts with
    | some file =>
      { place := ⟨file, 1⟩, what := "main is not written yet", why
        fix := s!"Add `def main : IO Unit := …` at the end of {file}, outside any namespace{calls}", next := .lint }
    | none =>
      { place := ⟨lakefileOf facts, 1⟩, what := "main is not written yet", why
        fix := s!"Add `def main : IO Unit := …` at the end of the WorldCode module that is the root of the lean_exe, \
          outside any namespace{calls}"
        next := .lint }
  | .unreachedHole hole =>
    let main := match facts.solution.main? with
      | some (_, place) => s!"main ({shownPlace place})"
      | none => "main"
    { place := hereOf facts hole, what := s!"hole {hole} is never called from main"
      why := "so the headlines about it say nothing about the program that runs"
      fix := s!"Call {hole} from {main}, or from code main runs", next := .lint }
  | .undecidedCheck use check =>
    { place := { check.place with line := max 1 check.place.line }
      what := s!"this Check cannot be matched against {use.statement}, which {use.headline} assumes, within the \
        audit's budget of {matchBudget} heartbeats"
      why := "so it does not count as a Check of it"
      fix := s!"Restate that Check with the arguments of the premise, as `Check {use.statement} …`", next := .lint }
  | .uncheckedClaim use =>
    let use := if use.statement.isEmpty then { use with statement := toString use.claim } else use
    let shown := claimShown facts use
    let variables := ((claimBinder? facts use).map (·.variables)).getD #[]
    let chosen := if variables.isEmpty then ""
      else s!", with a value of your choice in place of {" and ".intercalate variables.toList}"
    { place := hereOf facts use.headline, what := s!"{use.headline} assumes the world claim {shown}"
      why := "which no Check tests against the real foreign code"
      fix := s!"Add `Check {use.statement} := do …`, or `Check {use.statement} : <an instance it implies>`, to \
        {worldFile facts}{chosen}"
      next := .lint }
  | .hiddenDependency dependency =>
    let lakefile := lakefileOf facts
    let hides := fun (path : String) => sandboxHidden.any fun hidden =>
      (hidden.splitOn "/").isPrefixOf (path.splitOn "/")
    let dir := if hides dependency.configured then dependency.configured else dependency.real
    let what := s!"the comparator's sandbox hides package {dependency.name} at {dir}"
    let why := "because it mounts empty directories over /home, /root, /run, /tmp, and /var, so `lake comparator` \
      cannot build the solution"
    if dependency.overridden then
      { place := ⟨overridesFile, 1⟩, what, why
        fix := s!"In {overridesFile}, which overrides where lakefile.lean and lake-manifest.json locate \
          {dependency.name}, set its `dir` to a directory outside those, or delete its entry"
        next := .lint }
    else
      { place := ⟨lakefile, 1⟩, what, why
        fix := s!"{lakefile} and lake-manifest.json are owned, so the fix records a new statement: in {lakefile}, \
          require {dependency.name} from git, so that it lives in .lake/packages, or from a directory outside those, \
          run `lake update {dependency.name}`, delete owned.lock, and run `lake build` to record them"
        next := .lint }

end Lint

end SoftwareChallenge

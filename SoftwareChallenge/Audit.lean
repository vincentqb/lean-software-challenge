module

public meta import SoftwareChallenge.Commands

public section
meta section

open Lean

namespace SoftwareChallenge.Audit

private def closure (next : Name → Array Name) (roots : Array Name) : NameSet := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    pending := pending ++ next name
  return seen

private def terminates (env : Environment) (name : Name) : Bool :=
  (Elab.Structural.eqnInfoExt.find? env name).isSome || (Elab.WF.eqnInfoExt.find? env name).isSome

private def fixpoint (env : Environment) (name : Name) : Bool :=
  (Elab.PartialFixpoint.eqnInfoExt.find? env name).isSome

private def computational (info : ConstantInfo) : MetaM Bool := do
  unless info matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _ do return false
  if ← Meta.isProp info.type then return false
  Meta.forallTelescopeReducing info.type fun _ result => return !(← Meta.whnf result).isSort

private def meaningDependencies (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | some (.inductInfo ind) => ind.ctors.toArray
  | some (.ctorInfo constructor) => constructor.type.getUsedConstants
  | some info => ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  | none => #[]

private def dependingOn (env : Environment) (roots : Array Name) (target : Name) : NameSet :=
  let dependents := (closure (meaningDependencies env) roots).foldl (init := {})
    fun (map : Std.HashMap Name (Array Name)) name => (meaningDependencies env name).foldl
      (fun map dependency => map.insert dependency ((map.getD dependency #[]).push name)) map
  closure (dependents.getD · #[]) #[target]

private def recordedInOlean (name : Name) : Bool := !isPrivateName name

private def nonstandardAxioms (name : Name) : CoreM (Array Name) :=
  return (← collectAxioms name).filter (!standardAxioms.contains ·)

private partial def axiomsOf (name : Name) :
    StateRefT (Std.HashMap Name (Array Name)) CoreM (Array Name) := do
  if let some known := (← get)[name]? then return known
  modify (·.insert name #[])
  let found ← if recordedInOlean name then nonstandardAxioms name else
    match (← getEnv).find? name with
    | none => pure #[]
    | some info => do
      let mut found := if info.isAxiom && !standardAxioms.contains name then #[name] else #[]
      let uses := info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] ++
        match info with | .inductInfo ind => ind.ctors.toArray | _ => #[]
      for used in uses do
        found := found ++ (← axiomsOf used).filter (!found.contains ·)
      pure found
  modify (·.insert name found)
  return found

private def declaration (reachesIO terminating : NameSet) (info : ConstantInfo) (moduleName : Name) :
    StateRefT (Std.HashMap Name (Array Name)) CoreM DeclarationFact := do
  let env ← getEnv
  let generated := (← findDeclarationRangesCore? info.name).isNone
  let isComputational ← Meta.MetaM.run' <| computational info
  return {
    name := info.name
    moduleName
    computational := isComputational
    isUnsafe := info.isUnsafe
    isPartial := info.isPartial && !(generated && (Compiler.isUnsafeRecName? info.name).any fun source =>
      terminates env source || terminating.contains source && fixpoint env source)
    external := isExtern env info.name
    unfoldable := info matches .defnInfo _
    replaced := (Compiler.getImplementedBy? env info.name).isSome
    initializes := (getInitFnNameFor? env info.name).isSome
    effects := isComputational && info.type.getUsedConstants.any reachesIO.contains
    debug := info.getUsedConstantsAsSet.any fun n => n.isAtomic && "dbg".isPrefixOf n.toString
    axioms := ← axiomsOf info.name
  }

def collect (catalog : Array Name) (terminating : NameSet := {}) : CoreM Inventory := do
  modifyEnv (·.setExporting false)
  let env ← getEnv
  let modules ← catalog.mapM fun name => do
    let some idx := env.getModuleIdx? name | throwError "Compiled module {name} is unavailable"
    return (name, env.header.moduleData[idx.toNat]!)
  let types := modules.flatMap fun (_, data) => data.constants.flatMap (·.type.getUsedConstants)
  let reachesIO := dependingOn env types ``IO.RealWorld
  let declarations ← StateRefT'.run' (s := {}) <| modules.flatMapM fun (name, data) =>
    data.constants.mapM fun info => declaration reachesIO terminating info name
  return {
    modules := modules.map fun (name, data) =>
      { name, usesModuleSystem := data.isModule,
        imports := data.imports.map fun i => { name := i.module, comptime := i.isMeta } }
    declarations }

private def withEnvironment {α : Type} (modules : Array Name) (action : CoreM α) : IO α := do
  unsafe enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let (result, _) ← action.toIO { fileName := "<lean-software-challenge>", fileMap := default, maxHeartbeats := 0 } { env }
  return result

def challengeModule : Name := `Challenge

structure Challenge where
  theorems : Array Name := #[]
  holes : Array Name := #[]
  filled : Array Name := #[]
  kills : Array (Name × Name) := #[]
  terminating : Array (Name × Name) := #[]
  misshapen : Array (Name × Name) := #[]
  unmarked : Array (Name × Name) := #[]

def Challenge.headlines (challenge : Challenge) : Array Name :=
  challenge.theorems.filter fun name => !challenge.kills.any (·.1 == name)

def Challenge.killsOf (challenge : Challenge) (headline : Name) : Array Name :=
  (challenge.kills.filter (·.2 == headline)).map (·.1)

structure Termination where
  definition : Name
  headline : Name
  fixpoint : Bool
  mentioned : Bool

def terminations (env : Environment) (terminating : Array (Name × Name)) : Array Termination :=
  terminating.map fun (definition, headline) => {
    definition, headline
    fixpoint := fixpoint env definition
    mentioned := ((env.find? headline).map (·.type.getUsedConstants.contains definition)).getD false }

structure Assumption where
  claim : Name
  statement : String
  checks : Nat

structure Headline where
  name : Name
  assumptions : Array Assumption
  unnamed : Array String

def headline (evidence : Array Evidence) (name : Name) : MetaM Headline := do
  let env ← getEnv
  let some info := env.find? name | throwError "Headline {name} is not compiled"
  let (patterns, _, _) ← Meta.forallMetaTelescope info.type
  Meta.forallTelescope info.type fun binders _ => do
    let mut assumptions := #[]
    let mut unnamed := #[]
    for (binder, pattern) in binders.zip patterns do
      let statement ← Meta.inferType binder
      let claim := statement.getAppFn.constName
      if isWorldClaim env claim then
        let expected ← Meta.inferType pattern
        let checks ← (evidence.filter (·.claim == claim)).filterM fun found =>
          withoutModifyingState (Meta.isDefEq expected found.statement)
        let shown := toString (← Meta.ppExpr statement)
        unless assumptions.any (·.statement == shown) do
          assumptions := assumptions.push { claim, statement := shown, checks := checks.size }
      else if !statement.hasFVar && (← Meta.isProp statement) then
        unnamed := unnamed.push (toString (← Meta.ppExpr statement))
    return { name, assumptions, unnamed }

private partial def replacing (replaceable : NameSet) :
    Expr → Expr → StateT (NameMap Expr) Option Unit
  | .const name levels, target =>
    if replaceable.contains name then do
      guard !target.hasLooseBVars
      match (← get).find? name with
      | some witness => guard (witness == target)
      | none => modify (·.insert name target)
    else guard (target == .const name levels)
  | .app f a, .app g b => do replacing replaceable f g; replacing replaceable a b
  | .lam _ t b _, .lam _ u c _ | .forallE _ t b _, .forallE _ u c _ => do
    replacing replaceable t u; replacing replaceable b c
  | .mdata _ pattern, target | pattern, .mdata _ target => replacing replaceable pattern target
  | pattern, target => guard (pattern == target)

def kills (env : Environment) (replaceable : NameSet) (headline kill : Name) : Bool :=
  match env.find? headline, (env.find? kill).map (·.type) with
  | some headlineInfo, some (Expr.app (.const ``Not _) rejected) =>
    ((replacing replaceable headlineInfo.type rejected).run {}).isSome
  | _, _ => false

private def line (name : Name) : CoreM Nat :=
  return ((← findDeclarationRangesCore? name).map (·.range.pos.line)).getD 0

def readChallenge (project : Project) (challenge : Name) : IO Challenge := do
  let file ← findOLean challenge
  let parts ← #[file, file.addExtension "server", file.addExtension "private"].filterM (·.pathExists)
  let some (data, _) := (← readModuleDataParts parts).back?
    | throw <| .userError s!"{challenge} is not compiled"
  withEnvironment #[challenge] do
    let env ← getEnv
    let some index := env.getModuleIdx? challenge | throwError "{challenge} is not compiled"
    let declared := (← (data.constants.filter (!·.name.isInternal)).mapM fun info =>
      return (← line info.name, info)).qsort (·.1 < ·.1) |>.map (·.2)
    let usesSorry := fun (info : ConstantInfo) =>
      (info.value?.map (·.getUsedConstants.contains ``sorryAx)).getD false
    let foreign := (env.header.modules.zip env.header.moduleData).flatMap fun (module, data) =>
      if project.role? module.module == some .worldSpec then
        (data.constants.filter (isExtern env ·.name)).map (·.name)
      else #[]
    let holes := (declared.filter fun info => !info.isTheorem && usesSorry info).map (·.name)
    let found : Challenge := {
      theorems := (declared.filter (·.isTheorem)).map (·.name), holes
      filled := (declared.filter fun info => !info.isTheorem && !usesSorry info).map (·.name)
      kills := PersistentEnvExtension.getModuleEntries killsExt env index
      terminating := (PersistentEnvExtension.getModuleEntries terminatesExt env index).map
        fun (headline, hole) => (hole, headline) }
    let replaceable := NameSet.ofList (holes ++ foreign).toList
    let headlines := found.headlines
    return { found with
      misshapen := found.kills.filter fun (kill, headline) =>
        !headlines.contains headline || !kills env replaceable headline kill
      unmarked := headlines.flatMap fun headline =>
        (headlines.filter (kills env replaceable headline)).map (·, headline) }

def solutionOf (catalog : Array Name) : Except String Name :=
  match catalog.filter (· matches .str _ "Solution") with
  | #[solution] => .ok solution
  | #[] => .error "no module named Solution is built by a default target; name the module that proves \
      the headlines and kills Solution, e.g. MyApp.Solution, and build it from a default lean_lib"
  | several => .error s!"{", ".intercalate (several.map toString).toList} are all named Solution; \
      name only the module that proves the headlines and kills Solution"

def comparatorConfig (solution : Name) (challenge : Challenge) : String :=
  let quoted := fun (name : Name) => (toJson name).compress
  let names := fun (names : Array Name) => if names.isEmpty then "[]" else
    "[\n" ++ ",\n".intercalate (names.map (s!"    {quoted ·}")).toList ++ "\n  ]"
  let fields := [("challenge_module", quoted challengeModule), ("solution_module", quoted solution),
    ("theorem_names", names challenge.theorems), ("definition_names", names challenge.holes),
    ("permitted_axioms", names standardAxioms)]
  "{\n" ++ ",\n".intercalate (fields.map fun (key, value) => s!"  \"{key}\": {value}") ++ "\n}\n"

private def compiledCallees (env : Environment) (name : Name) : Array Name :=
  let compiled := (env.find? (Compiler.mkUnsafeRecName name)).orElse fun _ => env.find? name
  ((compiled.bind (·.value? (allowOpaque := true))).map (·.getUsedConstants)).getD #[]

def reachedFrom (env : Environment) (running : Name → Bool) (root : Name) : NameSet :=
  closure (fun name => (compiledCallees env name).filter running) #[root]

def entryOf (project : Project) (env : Environment) (moduleOf : Name → Option Name)
    (running : Name → Bool) (holes : Array Name) : Option (Option Name × Array Name) :=
  if !project.executable then none
  else if env.contains `main then
    some (moduleOf `main, holes.filter (!(reachedFrom env running `main).contains ·))
  else some (none, #[])

structure Facts where
  inventory : Inventory := ⟨#[], #[]⟩
  challenge : Challenge := {}
  headlines : Array Headline := #[]
  mentioned : NameSet := {}
  holes : Array (Name × Option Name) := #[]
  registrations : Array (Name × Option Role × Bool) := #[]
  entry : Option (Option Name × Array Name) := none
  challengeImports : Array Name := #[]
  terminations : Array Termination := #[]

private def roleRule : String :=
  "a module's role is the first component of its name that is CoreSpec, WorldSpec, CoreCode, or \
    WorldCode, and tooling otherwise, so rename a module to change its role, \
    e.g. MyApp.Helpers to MyApp.CoreCode.Helpers"

private def allowedImports : Role → String
  | .coreSpec => "CoreSpec modules and modules outside the package"
  | .worldSpec => "CoreSpec and WorldSpec modules and modules outside the package"
  | .coreCode => "CoreSpec and CoreCode modules and modules outside the package"
  | .worldCode => "any module but tooling"
  | .tooling => "any module"

private def remedy : Role → String
  | .coreSpec | .coreCode => "CoreSpec and CoreCode are pure: move effects and escape hatches to a WorldCode module"
  | .worldSpec => "declare foreign code as `@[extern] opaque` and move effects to a WorldCode module"
  | .worldCode => "WorldCode may do IO but not `unsafe`, `@[extern]`, or `@[implemented_by]`; \
      ask the owner to declare foreign code as `@[extern] opaque` in a WorldSpec module"
  | .tooling => "tooling may do anything but use axioms"

private def located (project : Project) (module : Name) : String :=
  match project.role? module with
  | some role => s!"{module} ({role})"
  | none => s!"{module}, outside the package"

private def distinct (errors : Array String) : Array String :=
  errors.foldl (fun kept error => if kept.contains error then kept else kept.push error) #[]

def sound (project : Project) (facts : Facts) : Array String := Id.run do
  let mut errors := #[]
  for fact in facts.inventory.modules do
    let some role := project.role? fact.name
      | errors := errors.push s!"{fact.name} is not a module of the challenge package; build it from a \
          lean_lib of the package"
    unless fact.usesModuleSystem do errors := errors.push s!"{fact.name}: start the file with `module`"
    for dependency in fact.imports do
      unless project.admits role dependency do
        errors := errors.push s!"{fact.name} ({role}) may not import {located project dependency.name}; \
          it may import {allowedImports role}; {roleRule}"
  for fact in facts.inventory.declarations do
    if let some role := project.role? fact.moduleName then
      let name := (Compiler.isUnsafeRecName? fact.name).getD fact.name
      unless fact.axioms.isEmpty do
        errors := errors.push s!"{name} ({role}) uses axiom {", ".intercalate (fact.axioms.map toString).toList}; \
          remove the axiom and prove the fact, or, if it is an assumption about the world, ask the owner to \
          state it as a WorldClaim"
      let reasons := fact.reasons role
      unless reasons.isEmpty do
        errors := errors.push s!"{name} ({role}): {", ".intercalate reasons}; {remedy role}"
  for (hole, module) in facts.holes do
    unless (module.bind project.role?) matches some .coreCode | some .worldCode do
      let place := (module.map fun module => s!"is defined in {located project module}").getD "is not defined"
      errors := errors.push s!"{hole}: a definition hole must be defined in a CoreCode or WorldCode module, \
        but it {place}; implement it in one; {roleRule}"
  if let some (module, unreached) := facts.entry then
    unless (module.bind project.role?) matches some .worldCode do
      errors := errors.push s!"main: the package declares a lean_exe, so declare main in a WorldCode module"
    for hole in unreached do errors := errors.push s!"{hole}: main never reaches this hole; call it from main"
  for t in facts.terminations do
    let marked := s!"@[terminates {t.definition}] on {t.headline} in Challenge.lean"
    unless t.fixpoint do
      errors := errors.push s!"{t.definition}: {marked} names it, but it is not a partial_fixpoint definition; \
        define it with partial_fixpoint, or ask the owner to drop the @[terminates]"
    unless facts.holes.any (·.1 == t.definition) do
      errors := errors.push s!"{t.definition}: {marked} names it, but it is not a definition hole; \
        ask the owner to name a hole declared with `sorry` in Challenge.lean"
    unless facts.challenge.headlines.contains t.headline && !(facts.challenge.killsOf t.headline).isEmpty do
      errors := errors.push s!"{t.definition}: {marked}, but {t.headline} is not a headline with a kill; \
        ask the owner to move the @[terminates] to a headline with a kill"
    unless t.mentioned do
      errors := errors.push s!"{t.definition}: {marked}, but {t.headline} does not mention it; \
        ask the owner to move the @[terminates] to a headline that states it returns"
  for line in facts.headlines do
    for hypothesis in line.unnamed do
      errors := errors.push s!"{line.name}: hypothesis {hypothesis} is not a WorldClaim; \
        ask the owner to declare it as one in a WorldSpec module, or to drop it"
  return distinct errors

def meaningful (facts : Facts) : Array String :=
  let challenge := facts.challenge
  (challenge.headlines.filterMap fun headline =>
    if !(challenge.killsOf headline).isEmpty || challenge.unmarked.any (·.1 == headline) then none
    else match challenge.unmarked.find? (·.2 == headline) with
      | some (kill, _) => some s!"{headline}: no kill shows it rejects a wrong implementation; \
          in Challenge.lean, mark {kill} `@[kills {headline}]`"
      | none => some s!"{headline}: no kill shows it rejects a wrong implementation; in Challenge.lean, \
          state `¬` {headline} with its holes replaced by wrong ones and mark it `@[kills {headline}]`") ++
  (challenge.misshapen.map fun (kill, headline) =>
    if challenge.headlines.contains headline then s!"{kill}: marked `@[kills {headline}]`, but it is not \
      `¬` {headline} with holes and WorldSpec foreign constants replaced by wrong ones; in Challenge.lean, \
      restate it as that negation, or name the headline it rejects"
    else s!"{kill}: marked `@[kills {headline}]`, but {headline} is not a headline of Challenge.lean; \
      name the headline it rejects") ++
  (facts.holes.filter (!facts.mentioned.contains ·.1)).map fun (hole, _) =>
    s!"{hole}: no headline mentions this hole; state one in Challenge.lean, or drop the hole"

def owned (project : Project) (facts : Facts) : Array String := Id.run do
  let mut errors := #[]
  for (claim, role, declaredThere) in facts.registrations do
    if role != some .worldSpec then
      errors := errors.push s!"{claim}: declare WorldClaims in a WorldSpec module"
    unless declaredThere do
      errors := errors.push s!"{claim}: registered outside the module that declares it; \
        register it with WorldClaim in the module that declares it"
  for dependency in facts.challengeImports do
    unless project.admits .worldSpec { name := dependency, comptime := false } do
      errors := errors.push s!"{challengeModule} imports {dependency}; \
        a challenge may import only CoreSpec and WorldSpec modules and modules outside the package"
  for name in facts.challenge.filled do
    errors := errors.push s!"{challengeModule} implements {name}; it only declares holes, so keep \
      `sorry` there and implement it in a CoreCode or WorldCode module"
  return errors

def lockErrors (locked current : Array (String × UInt64)) (edit : Array String) : Array String :=
  let restore := s!"restore it and edit {", ".intercalate edit.toList} instead; \
    the owner deletes owned.lock to record a new statement"
  (current.filterMap fun (file, digest) => match locked.find? (·.1 == file) with
    | none => some s!"{file} is owned but owned.lock does not record it; a module is owned when a component \
        of its name is CoreSpec or WorldSpec, so remove or rename it, or ask the owner to delete owned.lock \
        to record it"
    | some (_, recorded) => if recorded == digest then none
      else some s!"{file} changed since owned.lock; it decides what is claimed, so {restore}") ++
  (locked.filter fun (file, _) => !current.any (·.1 == file)).map fun (file, _) =>
    s!"{file} is recorded in owned.lock but missing; it decides what is claimed, so {restore}"

def evidenced (facts : Facts) : Array String :=
  facts.headlines.flatMap fun line => line.assumptions.filterMap fun assumption =>
    if assumption.checks > 0 then none
    else some s!"{line.name}: world claim {assumption.statement} has no Check; \
      add `Check {assumption.statement} ...` to a WorldCode module"

def challengeImports (file : System.FilePath) : IO (Array Name) := do
  return (← parseImports' (← IO.FS.readFile file) file.toString).imports.map (·.module)

private def ownedFiles (project : Project) (sources : Array (Name × String)) (challengeFile : String) :
    IO (Array String) := do
  let configuration ← #["lakefile.lean", "lake-manifest.json", "lean-toolchain"].filterM
    fun (file : String) => System.FilePath.pathExists file
  let claimModules := sources.filter (project.role? ·.1 matches some .coreSpec | some .worldSpec)
  return configuration ++ #["owned.lock", challengeFile] ++ claimModules.map (·.2)

private def editableFiles (project : Project) (sources : Array (Name × String)) : Array String :=
  (sources.filter (project.role? ·.1 matches some .coreCode | some .worldCode | some .tooling)).map (·.2)

private def readLock : IO (Option (Array (String × UInt64))) := do
  unless ← System.FilePath.pathExists "owned.lock" do return none
  return some <| ((← IO.FS.readFile "owned.lock").splitOn "\n").toArray.filterMap fun line =>
    match line.splitOn " " with
    | [digest, file] => digest.toNat?.map fun n => (file, n.toUInt64)
    | _ => none

private def digests (files : Array String) : IO (Array (String × UInt64)) :=
  (files.filter (· != "owned.lock")).mapM fun (file : String) => return (file, hash (← IO.FS.readFile file))

private def sharedNamespace (names : Array Name) : Name :=
  let common := fun (shared : List Name) (name : Name) =>
    (shared.zip name.getPrefix.components).takeWhile (fun (a, b) => a == b) |>.map (·.1)
  match names.toList with
  | [] => .anonymous
  | first :: rest => (rest.foldl common first.getPrefix.components).foldl (· ++ ·) .anonymous

def shorten (shared : Name) (name : Name) : String :=
  if shared != .anonymous && shared.isPrefixOf name && name != shared then
    toString (name.replacePrefix shared .anonymous)
  else toString name

private def describe (short : Name → String) (line : Headline) : String :=
  let assumed := line.assumptions.map fun assumption =>
    let label := if (line.assumptions.filter (·.claim == assumption.claim)).size > 1 then assumption.statement
      else short assumption.claim
    s!"{label} ({assumption.checks} {if assumption.checks == 1 then "check" else "checks"})"
  if assumed.isEmpty then short line.name else s!"{short line.name}  assumes {", ".intercalate assumed.toList}"

private def gather (project : Project) (catalog : Array Name) (challengeFile : String) : IO Facts := do
  let challenge ← readChallenge project challengeModule
  let facts ← withEnvironment catalog <| Meta.MetaM.run' do
    let env ← getEnv
    let moduleOf := fun (name : Name) =>
      (env.getModuleIdxFor? name).map (env.header.modules[·.toNat]!.module)
    let inventory ← collect catalog (NameSet.ofList (challenge.terminating.map (·.1)).toList)
    let running := fun name => (moduleOf name).any catalog.contains
    let evidence := (allEvidence env).filter fun found => (moduleOf found.source).any catalog.contains
    return {
      inventory, challenge
      headlines := ← challenge.headlines.mapM (headline evidence ·)
      mentioned := NameSet.ofList <| (challenge.headlines.flatMap fun name =>
        ((env.find? name).map (·.type.getUsedConstants)).getD #[]).toList
      holes := challenge.holes.map fun hole => (hole, moduleOf hole)
      registrations := catalog.flatMap fun module =>
        (PersistentEnvExtension.getModuleEntries claimsExt env (env.getModuleIdx? module).get!).map
          fun claim => (claim, project.role? module, moduleOf claim == some module)
      terminations := terminations env challenge.terminating
      entry := entryOf project env moduleOf running challenge.holes : Facts }
  return { facts with challengeImports := ← challengeImports challengeFile }

private def audit (executable : Bool) (challengeFile : String) (modules : List String) : IO UInt32 := do
  let sources := modules.toArray.map fun module => match module.splitOn "=" with
    | [name, file] => (name.toName, file)
    | _ => (module.toName, module)
  let catalog := sources.map (·.1)
  let project := Project.ofPackage catalog executable
  let facts ← gather project catalog challengeFile
  let edit := editableFiles project sources
  let ownedNow ← ownedFiles project sources challengeFile
  let current ← digests ownedNow
  let locked ← readLock
  let solution := solutionOf catalog
  let failures := (sound project facts).map ("sound: " ++ ·) ++ (meaningful facts).map ("meaningful: " ++ ·) ++
    ((match solution with | .ok _ => #[] | .error error => #[error]) ++ owned project facts ++ (locked.map (lockErrors · current edit)).getD #[]).map
      ("owned: " ++ ·) ++
    (evidenced facts).map ("evidence: " ++ ·)
  let files := s!"Edit: {" ".intercalate edit.toList}\nOwned: {" ".intercalate ownedNow.toList}"
  unless project.check facts.inventory && failures.isEmpty do
    IO.println ("\n".intercalate failures.toList ++ "\n" ++ files)
    return 1
  if let .ok solution := solution then
    let config := comparatorConfig solution facts.challenge
    unless (← try some <$> IO.FS.readFile "comparator.json" catch _ => pure none) == some config do
      IO.FS.writeFile "comparator.json" config
  if locked.isNone then
    IO.FS.writeFile "owned.lock" ("\n".intercalate (current.map fun (file, digest) => s!"{digest} {file}").toList)
  let short := shorten (sharedNamespace (facts.headlines.map (·.name)))
  for line in facts.headlines do IO.println (describe short line)
  for t in facts.terminations do IO.println s!"{short t.definition} terminates via {short t.headline}"
  IO.println files
  return 0

def run : List String → IO UInt32
  | "--executable" :: challengeFile :: modules => audit true challengeFile modules
  | challengeFile :: modules => audit false challengeFile modules
  | [] => do
    IO.println "usage: lean --run Audit.lean [--executable] <challenge file> <module>=<file>..."
    return 2

end SoftwareChallenge.Audit

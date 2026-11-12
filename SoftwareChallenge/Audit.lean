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

structure Config where
  challenge_module : Name
  solution_module : Name
  theorem_names : Array Name
  definition_names : Option (Array Name)
  terminates : Option (NameMap Name) := none
  deriving FromJson

def Config.holes (config : Config) : Array Name := config.definition_names.getD #[]

private def Config.terminating (config : Config) : Array (Name × Name) :=
  (config.terminates.getD {}).toList.toArray

structure Termination where
  definition : Name
  headline : Name
  fixpoint : Bool
  mentioned : Bool

def terminations (env : Environment) (config : Config) : Array Termination :=
  config.terminating.map fun (definition, headline) => {
    definition, headline
    fixpoint := fixpoint env definition
    mentioned := ((env.find? headline).map (·.type.getUsedConstants.contains definition)).getD false }

structure Headline where
  name : Name
  premises : Array Premise
  unnamed : Array String

def headline (listed : Array Name) (name : Name) : MetaM Headline := do
  let env ← getEnv
  let some info := env.find? name | throwError "Headline {name} is not compiled"
  let listedProof := fun (statement : Expr) => if statement.hasFVar || statement.hasMVar then none
    else listed.find? fun theorem_ => (env.find? theorem_).any (·.type == statement)
  Meta.forallTelescope info.type fun binders _ => do
    let mut premises := #[]
    let mut unnamed := #[]
    for binder in binders do
      let statement ← Meta.inferType binder
      let claim := statement.getAppFn.constName
      if let some kind := claimKind? env claim then
        premises := premises.push { claim, kind, dischargedBy := listedProof statement }
      else if !statement.hasFVar && (← Meta.isProp statement) then
        unnamed := unnamed.push (toString (← Meta.ppExpr statement))
    return { name, premises, unnamed }

private def withReplaceableAsMVars (replaceable : NameSet) (type : Expr) : MetaM Expr := do
  let mut pattern := type
  for name in type.getUsedConstants.filter replaceable.contains do
    let info ← getConstInfo name
    let mvar ← Meta.mkFreshExprMVar (info.instantiateTypeLevelParams
      (← info.levelParams.mapM fun _ => Meta.mkFreshLevelMVar))
    pattern := pattern.replace fun e => if e.isConstOf name then some mvar else none
  return pattern

def kills (replaceable : NameSet) (headline kill : Name) : MetaM Bool := do
  let some killInfo := (← getEnv).find? kill | return false
  let .app (.const ``Not _) rejected := killInfo.type | return false
  let some headlineInfo := (← getEnv).find? headline | return false
  withoutModifyingState <| Meta.withReducible <| Meta.withConfig (fun config => { config with
      foApprox := true, ctxApprox := true, quasiPatternApprox := true, constApprox := true }) <|
    Meta.isDefEq (← withReplaceableAsMVars replaceable headlineInfo.type) rejected

def killsOf (replaceable : NameSet) (theorems : Array Name) : MetaM (Array (Name × Array Name)) := do
  let found ← theorems.mapM fun headline => return (headline, ← theorems.filterM (kills replaceable headline))
  let killers := found.flatMap (·.2)
  return found.filter (!killers.contains ·.1)

private def compiledCallees (env : Environment) (name : Name) : Array Name :=
  let compiled := (env.find? (Compiler.mkUnsafeRecName name)).orElse fun _ => env.find? name
  ((compiled.bind (·.value? (allowOpaque := true))).map (·.getUsedConstants)).getD #[]

def reachedFrom (env : Environment) (running : Name → Bool) (root : Name) : NameSet :=
  closure (fun name => (compiledCallees env name).filter running) #[root]

def entryOf (project : Project) (env : Environment) (roleOf : Name → Option Role)
    (running : Name → Bool) (holes : Array Name) : Option (Name × Option Role × Array Name) :=
  project.entry.map fun entry =>
    if env.contains entry then
      (entry, roleOf entry, holes.filter (!(reachedFrom env running entry).contains ·))
    else (entry, none, #[])

structure Facts where
  inventory : Inventory := ⟨#[], #[]⟩
  evidence : Array Evidence := #[]
  headlines : Array Headline := #[]
  killsByHeadline : Array (Name × Array Name) := #[]
  mentioned : NameSet := {}
  holes : Array (Name × Option Role) := #[]
  registrations : Array (Name × Option Role × Bool) := #[]
  entry : Option (Name × Option Role × Array Name) := none
  challengeImports : Array Name := #[]
  challengeTheorems : Array Name := #[]
  challengeHoles : Array Name := #[]
  challengeFilled : Array Name := #[]
  terminations : Array Termination := #[]

private def allowedImports : Role → String
  | .spec | .boundary => "spec and boundary modules and trusted roots"
  | .core => "core, spec and boundary modules and trusted roots"
  | .shell => "any module but tooling"
  | .tooling => "any module"

private def remedy : Role → String
  | .spec | .core => "spec and core code is pure: move effects and escape hatches to a shell module"
  | .boundary => "a boundary module holds only `@[extern] opaque` declarations"
  | .shell => "shell code may do IO but not `unsafe`, `@[extern]`, or `@[implemented_by]`"
  | .tooling => "state an assumption as a WorldClaim hypothesis, not an axiom"

def sound (project : Project) (facts : Facts) : Array String := Id.run do
  let mut errors := #[]
  for fact in facts.inventory.modules do
    let some role := project.role? fact.name
      | errors := errors.push s!"Unclassified module {fact.name}; give it a role in Audit.lean"
    unless fact.usesModuleSystem do errors := errors.push s!"{fact.name}: start the file with `module`"
    for dependency in fact.imports do
      unless project.admits role dependency do
        errors := errors.push
          s!"{fact.name} ({repr role}) may not import {dependency.name}; it may import {allowedImports role}"
  for fact in facts.inventory.declarations do
    if let some role := project.role? fact.moduleName then
      let reasons := fact.reasons role
      unless reasons.isEmpty do
        errors := errors.push s!"{fact.name} ({repr role}): {", ".intercalate reasons}; {remedy role}"
  for (hole, role) in facts.holes do
    unless role matches some .core | some .shell do
      errors := errors.push s!"{hole}: a definition hole must be a core or shell definition"
  if let some (entry, role, unreached) := facts.entry then
    unless role matches some .shell do errors := errors.push s!"{entry}: declare it in a shell module"
    for hole in unreached do errors := errors.push s!"{hole}: {entry} never reaches this hole; call it from {entry}"
  for t in facts.terminations do
    unless t.fixpoint do
      errors := errors.push s!"{t.definition}: listed under terminates but not a partial_fixpoint definition"
    unless facts.holes.any (·.1 == t.definition) do
      errors := errors.push s!"{t.definition}: listed under terminates but not a definition hole"
    unless facts.killsByHeadline.any fun (name, found) => name == t.headline && !found.isEmpty do
      errors := errors.push s!"{t.definition}: terminates names {t.headline}, which is not a headline with a kill"
    unless t.mentioned do errors := errors.push s!"{t.definition}: {t.headline} does not mention it"
  for line in facts.headlines do
    for hypothesis in line.unnamed do
      errors := errors.push s!"{line.name}: hypothesis {hypothesis} is not a WorldClaim or Conjecture; \
        declare it as one in a spec module"
  return errors

def meaningful (facts : Facts) : Array String :=
  (facts.killsByHeadline.filterMap fun (headline, found) =>
    if found.isEmpty then some s!"{headline}: no kill shows it rejects a wrong implementation; state \
      `¬` the headline with its holes replaced by wrong ones in the challenge and comparator.json" else none) ++
  (facts.holes.filter (!facts.mentioned.contains ·.1)).map fun (hole, _) =>
    s!"{hole}: no headline mentions this hole; state one in the challenge, or drop it from comparator.json"


def owned (project : Project) (config : Config) (facts : Facts) : Array String := Id.run do
  let mut errors := #[]
  for (claim, role, declaredThere) in facts.registrations do
    if role.isSome && role != some .spec then
      errors := errors.push s!"{claim}: declare claims in a spec module"
    unless declaredThere do
      errors := errors.push s!"{claim}: registered outside the module that declares it"
  for dependency in facts.challengeImports do
    unless project.admits .spec { name := dependency, comptime := false } do
      errors := errors.push s!"{config.challenge_module} imports {dependency}; \
        a challenge may import only spec and boundary modules and trusted roots"
  for (field, declared, listed) in #[("theorem_names", facts.challengeTheorems, config.theorem_names),
      ("definition_names", facts.challengeHoles, config.holes)] do
    for name in declared.filter (!listed.contains ·) do
      errors := errors.push
        s!"{config.challenge_module} declares {name}, which comparator.json {field} omits; list it there"
    for name in listed.filter fun name => !declared.contains name && !facts.challengeFilled.contains name do
      errors := errors.push s!"comparator.json {field} lists {name}, which {config.challenge_module} \
        does not declare; declare it there with `sorry`, or drop it from comparator.json"
  for name in facts.challengeFilled.filter config.holes.contains do
    errors := errors.push s!"{config.challenge_module} implements {name}; it only declares it, so keep \
      `sorry` there and implement it in a core or shell module"
  return errors

def lockErrors (locked current : Array (String × UInt64)) (edit : Array String) : Array String :=
  let instead := s!"it decides what is claimed, so restore it and edit {", ".intercalate edit.toList} instead; \
    the owner deletes owned.lock to record a new statement"
  (current.filterMap fun (file, digest) => match locked.find? (·.1 == file) with
    | none => some s!"{file} is owned but owned.lock does not record it; {instead}"
    | some (_, recorded) => if recorded == digest then none else some s!"{file} changed since owned.lock; {instead}") ++
  (locked.filter fun (file, _) => !current.any (·.1 == file)).map fun (file, _) =>
    s!"{file} is recorded in owned.lock but missing; {instead}"

def evidenced (facts : Facts) : Array String :=
  facts.headlines.flatMap fun line => line.premises.filterMap fun premise =>
    if premise.kind == .world && !facts.evidence.any (·.claim == premise.claim) then
      some s!"{line.name}: world assumption {premise.claim} has no Test, Check, or live suite; add a Check \
        to its spec module or mark a suite `@[exercises {premise.claim}]`"
    else none

def challengeImports (challenge : Name) : IO (Array Name) := do
  let path := (← (← getSrcSearchPath).findWithExt "lean" challenge).getD
    (modToFilePath "." challenge "lean")
  return (← parseImports' (← IO.FS.readFile path) path.toString).imports.map (·.module)

private def challengeDeclarations (challenge : Name) : IO (Array Name × Array Name × Array Name) := do
  let file ← findOLean challenge
  let parts ← #[file, file.addExtension "server", file.addExtension "private"].filterM (·.pathExists)
  let some (data, _) := (← readModuleDataParts parts).back?
    | throw <| .userError s!"{challenge} is not compiled"
  let declared := data.constants.filter (!·.name.isInternal)
  let usesSorry := fun (info : ConstantInfo) =>
    (info.value?.map (·.getUsedConstants.contains ``sorryAx)).getD false
  return ((declared.filter (·.isTheorem)).map (·.name),
    (declared.filter fun info => !info.isTheorem && usesSorry info).map (·.name),
    (declared.filter fun info => !info.isTheorem && !usesSorry info).map (·.name))

private def sourceFile (module : Name) : String :=
  "/".intercalate (module.components.map toString) ++ ".lean"

private def ownedFiles (project : Project) (inventory : Inventory) (challenge : Name) : IO (Array String) := do
  let configuration ← #["comparator.json", "Audit.lean", "lakefile.lean", "lake-manifest.json",
    "lean-toolchain", "owned.lock"].filterM fun (file : String) => System.FilePath.pathExists file
  let claimModules := inventory.modules.filter (project.role? ·.name matches some .spec | some .boundary)
  return configuration ++ #[sourceFile challenge] ++ claimModules.map (sourceFile ·.name)

private def editableFiles (project : Project) (inventory : Inventory) : Array String :=
  (inventory.modules.filter (project.role? ·.name matches some .core | some .shell | some .tooling)).map
    (sourceFile ·.name)

private def readLock : IO (Option (Array (String × UInt64))) := do
  unless ← System.FilePath.pathExists "owned.lock" do return none
  return some <| ((← IO.FS.readFile "owned.lock").splitOn "\n").toArray.filterMap fun line =>
    match line.splitOn " " with
    | [digest, file] => digest.toNat?.map fun n => (file, n.toUInt64)
    | _ => none

private def digests (files : Array String) : IO (Array (String × UInt64)) :=
  (files.filter (· != "owned.lock")).mapM fun (file : String) => return (file, hash (← IO.FS.readFile file))

private def describe (evidence : Array Evidence) (premise : Premise) : String :=
  let found := evidence.filter (·.claim == premise.claim)
  let count := fun kind => (found.filter (·.kind == kind)).size
  let suites := found.filterMap fun e => if e.kind == .suite then some (toString e.source) else none
  let status := match premise.kind, premise.dischargedBy with
    | .world, _ => s!"world {premise.claim}"
    | _, some proof => s!"proved {premise.claim} by {proof}"
    | _, none => s!"open {premise.claim}"
  s!"{status} [{count .test} tests, {count .check} checks" ++
    (if suites.isEmpty then "]" else s!", suites {", ".intercalate suites.toList}]")

private def gather (project : Project) (config : Config) (catalog : Array Name) : IO Facts := do
  let facts ← withEnvironment catalog <| Meta.MetaM.run' do
    let env ← getEnv
    let moduleOf := fun (name : Name) =>
      (env.getModuleIdxFor? name).map (env.header.modules[·.toNat]!.module)
    let roleOf := fun (name : Name) => (moduleOf name).bind project.role?
    let inventory ← collect catalog (NameSet.ofList (config.terminating.map (·.1)).toList)
    let boundary := inventory.declarations.filter (project.role? ·.moduleName == some .boundary)
    let killsByHeadline ← killsOf (NameSet.ofList (config.holes ++ boundary.map (·.name)).toList)
      config.theorem_names
    let running := fun name => (moduleOf name).any fun module =>
      catalog.contains module && project.role? module != some .tooling
    return {
      inventory, killsByHeadline
      evidence := allEvidence env
      headlines := ← killsByHeadline.mapM (headline config.theorem_names ·.1)
      mentioned := NameSet.ofList <| (killsByHeadline.flatMap fun (name, _) =>
        ((env.find? name).map (·.type.getUsedConstants)).getD #[]).toList
      holes := config.holes.map fun hole => (hole, roleOf hole)
      registrations := catalog.flatMap fun module =>
        (PersistentEnvExtension.getModuleEntries claimsExt env (env.getModuleIdx? module).get!).map
          fun (claim, _) => (claim, project.role? module, moduleOf claim == some module)
      terminations := terminations env config
      entry := entryOf project env roleOf running config.holes : Facts }
  let (challengeTheorems, challengeHoles, challengeFilled) ← challengeDeclarations config.challenge_module
  return { facts with
    challengeTheorems, challengeHoles, challengeFilled
    challengeImports := ← challengeImports config.challenge_module }

def run (project : Project) (args : List String) : IO Unit := do
  let config : Config ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json") >>= fromJson?
  let catalog := args.toArray.map String.toName
  unless catalog.contains config.solution_module do
    throw <| .userError s!"solution_module {config.solution_module} is not built by a default target"
  let facts ← gather project config catalog
  let edit := editableFiles project facts.inventory
  let ownedNow ← ownedFiles project facts.inventory config.challenge_module
  let current ← digests ownedNow
  let locked ← readLock
  let failures := (sound project facts).map ("sound: " ++ ·) ++ (meaningful facts).map ("meaningful: " ++ ·) ++
    (owned project config facts ++ (locked.map (lockErrors · current edit)).getD #[]).map ("owned: " ++ ·) ++
    (evidenced facts).map ("evidence: " ++ ·)
  let files := s!"Edit: {" ".intercalate edit.toList}\nOwned: {" ".intercalate ownedNow.toList}"
  unless project.check facts.inventory && failures.isEmpty do
    throw <| IO.userError ("SoftwareChallenge audit failed:\n" ++ "\n".intercalate failures.toList ++ "\n" ++ files)
  if locked.isNone then
    IO.FS.writeFile "owned.lock" ("\n".intercalate (current.map fun (file, digest) => s!"{digest} {file}").toList)
  IO.println s!"Checked {facts.inventory.modules.size} modules and {facts.inventory.declarations.size} declarations"
  for (line, (_, found)) in facts.headlines.zip facts.killsByHeadline do
    let notes := line.premises.map (describe facts.evidence) |>.push
      s!"killed by {", ".intercalate (found.map toString).toList}"
    IO.println s!"{if proved line.premises then "●" else "◕"} {line.name}  ({"; ".intercalate notes.toList})"
  for t in facts.terminations do IO.println s!"{t.definition} terminates via {t.headline}"
  IO.println files

end SoftwareChallenge.Audit

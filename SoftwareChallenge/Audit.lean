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

def fixpoint (env : Environment) (name : Name) : Bool :=
  (Elab.PartialFixpoint.eqnInfoExt.find? env name).isSome

def derived (env : Environment) (name : Name) : Bool :=
  (Compiler.isUnsafeRecName? name).any fun source => Meta.isInstanceCore env source.getPrefix

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

private def directUses (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] ++
    match info with | .inductInfo ind => ind.ctors.toArray | _ => #[]

private partial def axiomsOf (name : Name) :
    StateRefT (Std.HashMap Name (Array Name)) CoreM (Array Name) := do
  if let some known := (← get)[name]? then return known
  modify (·.insert name #[])
  let found ← if recordedInOlean name then nonstandardAxioms name else
    match (← getEnv).find? name with
    | none => pure #[]
    | some info => do
      let mut found := if info.isAxiom && !standardAxioms.contains name then #[name] else #[]
      for used in directUses info do
        found := found ++ (← axiomsOf used).filter (!found.contains ·)
      pure found
  modify (·.insert name found)
  return found

private def ownAxioms (info : ConstantInfo) : StateRefT (Std.HashMap Name (Array Name)) CoreM (Array Name) := do
  let mut found := if info.isAxiom && !standardAxioms.contains info.name then #[info.name] else #[]
  for used in directUses info do
    if used == info.name then continue
    found := found ++ (← axiomsOf used).filter (!found.contains ·)
  return found

def ownInfo (env : Environment) (module name : Name) : Option ConstantInfo := do
  let index ← env.getModuleIdx? module
  env.header.moduleData[index.toNat]!.constants.find? (·.name == name)

private def culpritOf (bad start : Name) (own : Option ConstantInfo) :
    StateRefT (Std.HashMap Name (Array Name)) CoreM Name := do
  let env ← getEnv
  let mut frontier := #[start]
  let mut seen : NameSet := {}
  while !frontier.isEmpty do
    let mut next := #[]
    for name in frontier do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := (if name == start then own else none).orElse fun _ => env.find? name | continue
      let uses := directUses info
      if uses.contains bad then return name
      for used in uses do
        if !seen.contains used && (← axiomsOf used).contains bad then next := next.push used
    frontier := next
  return start

structure Blame where
  declaration : Name
  module : Name
  axiomName : Name
  culprit : Name
  culpritModule : Option Name

def blamesOf (inventory : Inventory) : CoreM (Array Blame) := StateRefT'.run' (s := {}) do
  let env ← getEnv
  let mut found := #[]
  for fact in inventory.declarations do
    for axiomName in fact.axioms do
      let culprit ← culpritOf axiomName fact.name (ownInfo env fact.moduleName fact.name)
      let culpritModule := (env.getModuleIdxFor? culprit).map (env.header.modules[·.toNat]!.module)
      found := found.push { declaration := fact.name, module := fact.moduleName, axiomName, culprit, culpritModule }
  return found

def nativeTactic? (name : Name) : Option Name :=
  match (privateToUserName name).components.dropWhile (· != `_native) with
  | _ :: tactic :: _ => some tactic
  | _ => none

def ownerOf (name : Name) : Name :=
  let user := privateToUserName name
  let kept := (user.components.takeWhile (!·.isInternalOrNum)).foldl (· ++ ·) .anonymous
  let kept := if kept.isAnonymous then user else kept
  match privatePrefix? name with
  | some prefixName => prefixName ++ kept
  | none => kept

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
    isPartial := info.isPartial && !(generated && (derived env info.name ||
      (Compiler.isUnsafeRecName? info.name).any fun source =>
        terminates env source || terminating.contains source && fixpoint env source))
    external := isExtern env info.name
    unfoldable := info matches .defnInfo _
    replaced := (Compiler.getImplementedBy? env info.name).isSome
    initializes := (getInitFnNameFor? env info.name).isSome
    effects := isComputational && info.type.getUsedConstants.any reachesIO.contains
    debug := info.getUsedConstantsAsSet.any fun n => n.isAtomic && "dbg".isPrefixOf n.toString
    axioms := ← ownAxioms info
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

private def withEnvironment {α : Type} (modules : Array Name) (action : CoreM α)
    (artifacts : NameMap ImportArtifacts := {}) : IO α := do
  unsafe enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true) (arts := artifacts)
  let (result, _) ← action.toIO { fileName := "<lean-software-challenge>", fileMap := default, maxHeartbeats := 0 } { env }
  return result

def rangesIn (env : Environment) (index : ModuleIdx) (name : Name) : Option DeclarationRanges :=
  let find := fun (level : OLeanLevel) =>
    ((declRangeExt.toPersistentEnvExtension.getModuleEntries env index (level := level)).binSearch (name, default)
      (fun a b => Name.quickLt a.1 b.1)).map (·.2)
  (find .exported).orElse fun _ => find .server

def declarationParents (env : Environment) (inventory : Inventory) : Std.HashMap Name Name :=
  inventory.declarations.foldl (init := {}) fun parents fact =>
    let parent := match env.find? fact.name with
      | some (.ctorInfo info) => some info.induct
      | some (.recInfo _) => some fact.name.getPrefix
      | _ => match env.getProjectionFnInfo? fact.name with
        | some projection => some projection.ctorName.getPrefix
        | none => if isAuxRecursor env fact.name || isNoConfusion env fact.name then some fact.name.getPrefix
          else none
    match parent with
    | some parent => parents.insert fact.name parent
    | none => parents

def declarationLines (env : Environment) (catalog : Array Name) : Std.HashMap (Name × Name) Nat := Id.run do
  let mut lines := {}
  for module in catalog do
    if let some index := env.getModuleIdx? module then
      for info in env.header.moduleData[index.toNat]!.constants do
        if let some ranges := rangesIn env index info.name then
          lines := lines.insert (module, info.name) ranges.range.pos.line
  return lines

def duplicatesIn (env : Environment) (catalog : Array Name) : Array (Name × Name × Name) := Id.run do
  let mut declaredIn : Std.HashMap Name (Array Name) := {}
  for module in catalog do
    if let some index := env.getModuleIdx? module then
      for info in env.header.moduleData[index.toNat]!.constants do
        if (rangesIn env index info.name).isSome then
          declaredIn := declaredIn.insert info.name ((declaredIn.getD info.name #[]).push module)
  let found := declaredIn.fold (init := #[]) fun found name modules =>
    if modules.size < 2 then found else
      let kept := ((env.getModuleIdxFor? name).map (env.header.modules[·.toNat]!.module)).getD modules[0]!
      found ++ (modules.filter (· != kept)).map (name, kept, ·)
  return found.qsort fun a b => toString a.1 < toString b.1

def challengeModule : Name := `Challenge

structure Preconditions where
  headline : Name
  expected : String
  premises : List Shape
  inputs : List (Universe × Shape)
  preconditions : List Shape
  mentions : Option Name
  inInput : Bool := false

structure Termination where
  definition : Name
  headline : Name
  fixpoint : Bool
  mentioned : Bool

def terminations (fixpoint : Name → Bool) (terminating : Array (Name × Name)) (stated : Name → Option Expr) :
    Array Termination :=
  terminating.map fun (definition, headline) => {
    definition, headline
    fixpoint := fixpoint definition
    mentioned := ((stated headline).map (·.getUsedConstants.contains definition)).getD false }

structure Challenge where
  theorems : Array Name := #[]
  statements : Array (Name × Expr) := #[]
  holes : Array Name := #[]
  filled : Array Name := #[]
  axioms : Array Name := #[]
  privates : Array (Name × Nat) := #[]
  derivedPartials : Array (Name × Name × Option Nat) := #[]
  kills : Array (Name × Name) := #[]
  witnesses : Array (Name × Name) := #[]
  preconditioned : Array Preconditions := #[]
  misshapenWitnesses : Array (Name × Name) := #[]
  independent : Array (Name × Name) := #[]
  terminating : Array (Name × Name) := #[]
  misshapen : Array (Name × Name) := #[]
  unreplaced : Array (Name × Name) := #[]
  unmarked : Array (Name × Name) := #[]
  declared : Array ConstantInfo := #[]
  lines : Array (Name × Nat) := #[]
  signatures : Array (Name × String) := #[]
  written : Array (Name × String) := #[]
  rendered : Array (Name × String × String) := #[]
  templates : Array (Name × String) := #[]
  fixed : Array Name := #[]
  auxiliaries : Array (Name × Array ConstantInfo) := #[]
  hypotheses : Array (Name × Array String) := #[]
  aboutHoles : Array (Name × Array (String × Name)) := #[]

def Challenge.headlines (challenge : Challenge) : Array Name :=
  challenge.theorems.filter fun name => !challenge.kills.any (·.1 == name) && !challenge.witnesses.any (·.1 == name)

def Challenge.killsOf (challenge : Challenge) (headline : Name) : Array Name :=
  (challenge.kills.filter (·.2 == headline)).map (·.1)

def Challenge.witnessesOf (challenge : Challenge) (headline : Name) : Array Name :=
  (challenge.witnesses.filter (·.2 == headline)).map (·.1)

def Challenge.statement? (challenge : Challenge) (name : Name) : Option Expr :=
  (challenge.statements.find? (·.1 == name)).map (·.2)

def Challenge.lineOf (challenge : Challenge) (name : Name) : Nat :=
  ((challenge.lines.find? (·.1 == name)).map (·.2)).getD 0

def Challenge.renderedOf (challenge : Challenge) (name : Name) : String × String :=
  ((challenge.rendered.find? (·.1 == name)).map (·.2)).getD ("", "")

def Challenge.writtenOf (challenge : Challenge) (name : Name) : String :=
  ((challenge.written.find? (·.1 == name)).map (·.2)).getD (toString name)

def namespaceOf (full : Name) (written : String) : Name :=
  let whole := full.components
  let tail := written.toName.components
  if !tail.isEmpty && tail.length ≤ whole.length && whole.drop (whole.length - tail.length) == tail then
    (whole.take (whole.length - tail.length)).foldl (· ++ ·) .anonymous
  else .anonymous

def Challenge.namespaceOf (challenge : Challenge) (name : Name) : Name :=
  SoftwareChallenge.Audit.namespaceOf name (challenge.writtenOf name)

def Challenge.keywordOf (challenge : Challenge) (name : Name) : String :=
  if challenge.holes.contains name then "def" else "theorem"

def Challenge.signatureOf (challenge : Challenge) (name : Name) : String :=
  let keyword := challenge.keywordOf name
  match challenge.signatures.find? (·.1 == name) with
  | some (_, signature) => s!"{keyword} {challenge.writtenOf name} {signature}"
  | none => s!"{keyword} {challenge.writtenOf name} : {(challenge.renderedOf name).1}"

def Challenge.purpose (challenge : Challenge) (name : Name) : String :=
  match challenge.kills.find? (·.1 == name), challenge.witnesses.find? (·.1 == name) with
  | some (_, headline), _ => s!"so nothing shows that {headline} rejects a wrong implementation"
  | _, some (_, headline) => s!"so nothing shows that some input meets the preconditions of {headline}"
  | none, none => if challenge.holes.contains name then "so no headline about it can be proved"
    else "so the solution does not claim it yet"
structure Assumption where
  claim : Name
  statement : String
  checks : Nat
  unused : Bool := false
  checkStatement : String := statement
  checkVariables : Array String := #[]

structure Unmatched where
  premise : String
  module : Option Name
  line : Nat

structure Headline where
  name : Name
  assumptions : Array Assumption
  unnamed : Array String
  aboutHoles : Array (String × Name) := #[]
  unmatched : Array Unmatched := #[]
  proved : Bool := true
  marker : String := "not yet proved"
  unlinted : Option Name := none
  killMark : Option String := none
  witnessMark : Option String := none

def matchBudget : Nat := 200000

def matchWithin (budget : Nat) (expected statement : Expr) : MetaM (Option Bool) :=
  withoutModifyingState <| tryCatchRuntimeEx
    (some <$> withCurrHeartbeats (withTheReader Core.Context ({ · with maxHeartbeats := budget * 1000 })
      (Meta.isDefEq expected statement)))
    fun _ => pure none

def abbreviates (project : Project) (name : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo info) := env.find? name | return false
  let module := (env.getModuleIdxFor? name).map (env.header.modules[·.toNat]!.module)
  unless !isWorldClaim env name && (module.bind project.role?) matches some .coreSpec | some .worldSpec do
    return false
  Meta.forallTelescopeReducing info.type fun _ result => return (← Meta.whnf result).isProp

partial def unfoldedClaim (project : Project) (type : Expr) : MetaM Expr := do
  match type with
  | .forallE name binder body info => return .forallE name binder (← unfoldedClaim project body) info
  | .mdata _ expr => unfoldedClaim project expr
  | _ =>
    let .const name _ := type.getAppFn | return type
    unless ← abbreviates project name do return type
    let some expanded ← Meta.delta? type (· == name) | return type
    unfoldedClaim project expanded

def claimOf (project : Project) (statement : Expr) : MetaM Name :=
  return conclusionHead (← unfoldedClaim project statement)

partial def unfolded (project : Project) (type : Expr) : MetaM Expr :=
  Meta.forallTelescope type fun binders body => do
    let body := body.consumeMData
    let .const name _ := body.getAppFn | return type
    unless ← abbreviates project name do return type
    let some expanded ← Meta.delta? body (· == name) | return type
    Meta.mkForallFVars binders (← unfolded project expanded)

def headline (project : Project) (evidence : Array Evidence) (name : Name) (written : Expr)
    (prover : Option Name := none) (budget : Nat := matchBudget) (replaceable : NameSet := {}) :
    MetaM Headline := do
  let env ← getEnv
  let type ← unfolded project written
  let record := prover.bind (premiseRecord? env · name)
  let (patterns, _, _) ← Meta.forallMetaTelescope type
  Meta.forallTelescope type fun binders _ => do
    let mut assumptions : Array Assumption := #[]
    let mut unnamed := #[]
    let mut aboutHoles := #[]
    let mut unmatched := #[]
    for ((binder, pattern), index) in (binders.zip patterns).zipIdx do
      let statement ← Meta.inferType binder
      let claim ← claimOf project statement
      if isWorldClaim env claim then
        let (_, _, expected) ← Meta.forallMetaTelescope (← unfoldedClaim project (← Meta.inferType pattern))
        let shown := toString (← Meta.ppExpr statement)
        let (checkStatement, checkVariables) ← Meta.forallTelescope (← unfoldedClaim project statement)
            fun peeled conclusion => do
          let chosen ← peeled.filterMapM fun bound => do
            if ← Meta.isProp (← Meta.inferType bound) then return none
            return some (toString (← bound.fvarId!.getUserName))
          return (toString (← Meta.ppExpr conclusion), chosen)
        let mut checks := 0
        for found in evidence.filter (·.claim == claim) do
          match ← matchWithin budget expected found.statement with
          | some true => checks := checks + 1
          | some false => pure ()
          | none =>
            let module := (env.getModuleIdxFor? found.source).map (env.header.modules[·.toNat]!.module)
            unmatched := unmatched.push { premise := checkStatement, module, line := found.line }
        let unused := record.any (·.contains (index, false))
        match assumptions.findIdx? (·.statement == shown) with
        | some known => assumptions := assumptions.modify known fun a => { a with unused := a.unused && unused }
        | none =>
          assumptions := assumptions.push
            { claim, statement := shown, checks, unused, checkStatement, checkVariables }
      else if !statement.hasFVar && (← Meta.isProp statement) then
        let shown := toString (← Meta.ppExpr statement)
        match statement.getUsedConstants.find? replaceable.contains with
        | some hole => aboutHoles := aboutHoles.push (shown, hole)
        | none => unnamed := unnamed.push shown
    return { name, assumptions, unnamed, aboutHoles, unmatched, proved := prover.isSome,
             unlinted := if record.isNone then prover else none }

def toUniverse : Level → Universe
  | .zero => .zero
  | .succ level => .succ (toUniverse level)
  | .max left right => .max (toUniverse left) (toUniverse right)
  | .imax left right => .imax (toUniverse left) (toUniverse right)
  | .param name => .param name
  | .mvar id => .mvar id.name

@[expose] def toShape : Expr → Shape
  | .bvar index => .bvar index
  | .fvar id => .fvar id.name
  | .mvar id => .mvar id.name
  | .sort level => .sort (toUniverse level)
  | .const name levels => .const name (levels.map toUniverse)
  | .app function argument => .app (toShape function) (toShape argument)
  | .lam _ type body _ => .lam (toShape type) (toShape body)
  | .forallE _ type body _ => .forallE (toShape type) (toShape body)
  | .letE _ type value body _ => .letE (toShape type) (toShape value) (toShape body)
  | .lit (.natVal value) => .natLit value
  | .lit (.strVal value) => .strLit value
  | .mdata _ expr => toShape expr
  | .proj structureName index value => .proj structureName index (toShape value)

theorem toShape_mdata (data : MData) (expr : Expr) : toShape (.mdata data expr) = toShape expr := rfl

def kills (env : Environment) (replaceable : NameSet) (headline kill : Name) : Bool :=
  match env.find? headline, (env.find? kill).map (toShape ·.type) with
  | some headlineInfo, some (.app (.const ``Not _) rejected) =>
    let stated := toShape headlineInfo.type
    (stated.witnesses? replaceable.contains rejected).isSome && stated != rejected
  | _, _ => false

private def normalized (expr : Expr) : Expr := expr.replaceLevel (some ·.normalize)

def preconditionsOf (project : Project) (replaceable : NameSet) (headline : Name) (type : Expr) :
    MetaM (Option Preconditions) := do
  Meta.forallTelescope (← unfolded project type) fun binders _ => do
    let env ← getEnv
    let mut inputs := #[]
    let mut premises := #[]
    let mut preconditions := #[]
    for (binder, index) in binders.zipIdx do
      let statement ← Meta.inferType binder
      let depended ← (binders.extract (index + 1) binders.size).anyM fun later =>
        return (← Meta.inferType later).containsFVar binder.fvarId!
      if !(← Meta.isProp statement) || depended then inputs := inputs.push binder
      else if isWorldClaim env (← claimOf project statement) then
        unless statement.hasFVar do premises := premises.push statement
      else if statement.hasFVar then preconditions := preconditions.push statement
    let typed ← inputs.filterM fun input => return (← Meta.inferType input).getUsedConstants.any replaceable.contains
    if preconditions.isEmpty && typed.isEmpty then return none
    let mut used := #[]
    for input in inputs.reverse do
      let mentioned := fun (expr : Expr) => expr.containsFVar input.fvarId!
      if typed.contains input || (← Meta.isProp (← Meta.inferType input)) || preconditions.any mentioned ||
          (← used.anyM fun later => return mentioned (← Meta.inferType later)) then
        used := used.push input
    used := used.reverse
    let mut expected := mkAndN preconditions.toList
    let mut quantified := #[]
    for (input, index) in used.zipIdx.reverse do
      let type ← Meta.inferType input
      let level := (← Meta.getLevel type).normalize
      expected := mkApp2 (.const ``Exists [level]) type (← Meta.mkLambdaFVars #[input] expected)
      quantified := quantified.push (toUniverse level, toShape (normalized (type.abstract (used.extract 0 index))))
    expected := premises.foldr (fun premise body => .forallE `_ premise body .default) expected
    let inPrecondition := preconditions.findSome? fun statement => statement.getUsedConstants.find? replaceable.contains
    let inInputType ← typed.findSomeM? fun input => return (← Meta.inferType input).getUsedConstants.find? replaceable.contains
    return some {
      headline
      expected := toString (← Meta.ppExpr expected)
      premises := (premises.map (toShape ∘ normalized)).toList
      inputs := quantified.reverse.toList
      preconditions := (preconditions.map fun statement => toShape (normalized (statement.abstract used))).toList
      mentions := inPrecondition.orElse fun _ => inInputType
      inInput := inPrecondition.isNone && inInputType.isSome }

def Preconditions.witnessedBy (preconditions : Preconditions) (witness : Expr) : Bool :=
  Shape.applies preconditions.premises preconditions.inputs preconditions.preconditions (toShape (normalized witness))

def independent (env : Environment) (replaceable : NameSet) (headlines : Array Name) (headline kill : Name) :
    Bool :=
  let shape := fun name => (env.find? name).map (toShape ·.type)
  match shape headline, shape kill, (headlines.filter (· != headline)).mapM shape with
  | some stated, some rejected, some others =>
    stated.independent replaceable.contains others.toList rejected && stated.independence others.toList != rejected
  | _, _, _ => false

def unreplaced (env : Environment) (headlines : Array Name) (headline kill : Name) : Bool :=
  let shape := fun name => (env.find? name).map (toShape ·.type)
  match shape headline, shape kill, (headlines.filter (· != headline)).mapM shape with
  | some stated, some rejected, others =>
    stated.negation == rejected ||
      others.any fun others => !others.isEmpty && stated.independence others.toList == rejected
  | _, _, _ => false


def oneLine (text : String) : String :=
  " ".intercalate ((text.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))

private def lastOf : Name → String
  | .str _ last => last
  | name => toString name

private def signatureEnd : List Char → Nat → List Char → Option (List Char)
  | ':' :: '=' :: _, 0, kept => some kept.reverse
  | char :: rest, depth, kept =>
    signatureEnd rest (if "([{⦃⟨".contains char then depth + 1 else if ")]}⦄⟩".contains char then depth - 1
      else depth) (char :: kept)
  | [], _, _ => none

def signatureAt (source : String) (position : Position) : Option String := do
  let lines := source.splitOn "\n"
  let first ← lines[position.line - 1]?
  let text := "\n".intercalate (String.ofList (first.toList.drop position.column) :: lines.drop position.line)
  let signature := oneLine (String.ofList (← signatureEnd text.toList 0 []))
  if signature.isEmpty then none else some signature

def textAt (source : String) (range : DeclarationRange) : Option String := do
  guard (range.pos.line == range.endPos.line)
  let line ← (source.splitOn "\n")[range.pos.line - 1]?
  let text := String.ofList ((line.toList.drop range.pos.column).take (range.endPos.column - range.pos.column))
  if text.isEmpty then none else some text

def lineAt (source : String) (line : Nat) : Option String := do
  let text := (← (source.splitOn "\n")[line - 1]?).trimAscii.toString
  if text.isEmpty then none else some text

def render (expr : Expr) : MetaM (String × String) := do
  let shown := fun (explicit : Bool) => withOptions (fun options => ((options.setBool `pp.proofs true).setBool
    `pp.explicit explicit).setBool `pp.universes explicit) do return oneLine (toString (← Meta.ppExpr expr))
  return (← shown false, ← shown true)

def killTemplate (type : Expr) (replaced : Array Name) : MetaM String := do
  let mut holes : Std.HashMap Name Expr := {}
  for name in replaced do
    if let some (.const _ levels) := type.find? (·.isConstOf name) then
      let hole := .const name levels
      holes := holes.insert name (← Meta.mkFreshExprMVar (← Meta.inferType hole)
        (userName := Name.mkSimple s!"wrong_{lastOf name}"))
  let held := holes
  let wrong := type.replace fun expr => match expr with
    | .const name _ => held[name]?
    | _ => none
  return oneLine (toString (← Meta.ppExpr (mkNot wrong)))

def auxiliariesOf (env : Environment) (inChallenge : Name → Bool) (targets : NameSet) (root : ConstantInfo) :
    Array ConstantInfo :=
  let auxiliary := fun (name : Name) => inChallenge name && !targets.contains name
  let uses := fun (name : Name) => match env.find? name with
    | some info => (info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]).filter auxiliary
    | none => #[]
  ((closure uses (root.type.getUsedConstants.filter auxiliary)).toArray.filterMap env.find?).qsort
    (toString ·.name < toString ·.name)

def readChallenge (project : Project) (challenge : Name) (olean : System.FilePath) (source : String := "") :
    IO Challenge := do
  let parts ← #[olean, olean.addExtension "server", olean.addExtension "private"].filterM (·.pathExists)
  let ir ← #[olean.withExtension "ir.sig", olean.withExtension "ir"].filterM (·.pathExists)
  let some (data, _) := (← readModuleDataParts parts).back?
    | throw <| .userError s!"{challenge} is not compiled"
  let artifacts : NameMap ImportArtifacts := .insert {} challenge (.ofArrays #[parts, ir])
  withEnvironment (artifacts := artifacts) #[challenge] do
    let env ← getEnv
    let some index := env.getModuleIdx? challenge | throwError "{challenge} is not compiled"
    let written ← (data.constants.filter (!·.name.isInternal)).filterMapM fun info => do
      return (← findDeclarationRangesCore? info.name).map (·, info)
    let written := written.qsort (·.1.range.pos.line < ·.1.range.pos.line)
    let privates ← (data.constants.filter fun info =>
        isPrivateName info.name && !(privateToUserName info.name).isInternal).filterMapM fun info => do
      return (← findDeclarationRangesCore? info.name).map fun ranges => (info.name, ranges.range.pos.line)
    let declared := written.map (·.2)
    let usesSorry := fun (info : ConstantInfo) =>
      (info.value?.map (·.getUsedConstants.contains ``sorryAx)).getD false
    let foreign := (env.header.modules.zip env.header.moduleData).flatMap fun (module, data) =>
      if project.role? module.module == some .worldSpec then
        (data.constants.filter (isExtern env ·.name)).map (·.name)
      else #[]
    let holes := (declared.filter fun info => !info.isTheorem && usesSorry info).map (·.name)
    let targets := declared.filter fun info => info.isTheorem || holes.contains info.name
    let targetNames := NameSet.ofList (targets.map (·.name)).toList
    let inChallenge := fun (name : Name) => env.getModuleIdxFor? name == some index
    let found : Challenge := {
      theorems := (declared.filter (·.isTheorem)).map (·.name), holes, privates
      statements := (declared.filter (·.isTheorem)).map fun info => (info.name, info.type)
      filled := (declared.filter fun info => !info.isTheorem && !info.isAxiom && !usesSorry info).map (·.name)
      axioms := (declared.filter (·.isAxiom)).map (·.name)
      kills := PersistentEnvExtension.getModuleEntries killsExt env index
      witnesses := PersistentEnvExtension.getModuleEntries witnessExt env index
      terminating := (PersistentEnvExtension.getModuleEntries terminatesExt env index).map
        fun (headline, hole) => (hole, headline)
      declared := targets
      lines := written.map fun (ranges, info) => (info.name, ranges.range.pos.line)
      signatures := written.filterMap fun (ranges, info) =>
        (signatureAt source ranges.selectionRange.endPos).map (info.name, ·)
      written := written.filterMap fun (ranges, info) => (textAt source ranges.selectionRange).map (info.name, ·)
      auxiliaries := targets.map fun info => (info.name, auxiliariesOf env inChallenge targetNames info) }
    let replaceable := NameSet.ofList (holes ++ foreign).toList
    let derivedPartials ← (env.header.modules.zip env.header.moduleData).flatMapM fun (module, data) => do
      unless project.role? module.module matches some .coreSpec | some .worldSpec do return #[]
      data.constants.filterMapM fun info => do
        unless info.isPartial && derived env info.name do return none
        let shown := ownerOf info.name
        let ranges ← match ← findDeclarationRangesCore? shown with
          | some ranges => pure (some ranges)
          | none => findDeclarationRangesCore? shown.getPrefix
        return some (shown, module.module, ranges.map (·.range.pos.line))
    let headlines := found.headlines
    let (preconditioned, rendered, hypotheses, aboutHoles, templates) ← Meta.MetaM.run' do
      let preconditioned ← headlines.filterMapM fun headline => match env.find? headline with
        | some info => preconditionsOf project replaceable headline info.type
        | none => pure none
      let rendered ← targets.mapM fun info => return (info.name, ← render info.type)
      let read ← headlines.filterMapM fun name => do
        let some info := env.find? name | return none
        return some (name, ← headline project #[] name info.type (replaceable := replaceable))
      let hypotheses := read.filterMap fun (name, line) => if line.unnamed.isEmpty then none else some (name, line.unnamed)
      let aboutHoles := read.filterMap fun (name, line) =>
        if line.aboutHoles.isEmpty then none else some (name, line.aboutHoles)
      let templates ← headlines.filterMapM fun name => do
        let some info := env.find? name | return none
        let used := info.type.getUsedConstants
        let replaced := if used.any holes.contains then used.filter holes.contains else used.filter foreign.contains
        if replaced.isEmpty then return none
        return some (name, ← killTemplate info.type replaced)
      return (preconditioned, rendered, hypotheses, aboutHoles, templates)
    let witnessed := fun (witness headline : Name) =>
      match preconditioned.find? (·.headline == headline), env.find? witness with
      | some preconditions, some info => preconditions.witnessedBy info.type
      | _, _ => false
    let unmarked := headlines.flatMap fun headline =>
      (headlines.filter (kills env replaceable headline)).map (·, headline)
    return { found with
      preconditioned, rendered, hypotheses, aboutHoles, templates, unmarked, derivedPartials
      fixed := headlines.filter fun name => !templates.any (·.1 == name) && !unmarked.any (·.1 == name)
      misshapenWitnesses := found.witnesses.filter fun (witness, headline) => !witnessed witness headline
      misshapen := found.kills.filter fun (kill, headline) => !headlines.contains headline ||
        !(kills env replaceable headline kill || independent env replaceable headlines headline kill)
      unreplaced := found.kills.filter fun (kill, headline) =>
        headlines.contains headline && unreplaced env headlines headline kill
      independent := found.kills.filterMap fun (kill, headline) =>
        if headlines.contains headline && independent env replaceable headlines headline kill then some (headline, kill)
        else none }

def solutionOf (catalog : Array Name) : Except String Name :=
  match catalog.filter (· matches .str _ "Solution") with
  | #[solution] => .ok solution
  | #[] =>
    let module := ((catalog[0]?.map (·.getRoot)).getD `MyApp) ++ `Solution
    .error s!"the package builds no module named Solution, so the comparator has no proofs to check. Create \
      {"/".intercalate (module.components.map toString)}.lean, proving the headlines, kills, and witnesses, and \
      add `{module}` to the roots of the default lean_lib in lakefile.lean if it is not there; lakefile.lean is \
      owned, so then delete owned.lock if it exists. Then run `lake build`."
  | several => .error s!"{", ".intercalate (several.map toString).toList} are all named Solution, but the \
      comparator checks one module. Rename all but the module that proves the headlines, kills, and witnesses, \
      then run `lake build`."

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
    let reached := reachedFrom env running `main
    some (moduleOf `main, holes.filter (!reached.contains ·))
  else some (none, #[])

def importClosure (env : Environment) (root : Name) : NameSet :=
  closure (fun module => match env.getModuleIdx? module with
    | some index => env.header.moduleData[index.toNat]!.imports.map (·.module)
    | none => #[]) #[root]

inductive Standing where
  | holds (module : Name)
  | unsound (module : Name)
  | absent
  | outside (module : Name)
  | kind (module : Name) (found : String)
  | universes (module : Name) (found : List Name)
  | differs (module : Name) (plain explicit : String)
  | auxiliary (module : Name) (constant : Name)
  deriving Inhabited

def Standing.marker : Standing → String
  | .absent | .unsound _ => "not yet proved"
  | .outside _ => "outside Solution's imports"
  | _ => "stated differently"

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "an axiom"
  | .defnInfo info => match info.safety with
    | .safe => "a def"
    | .unsafe => "an unsafe def"
    | .partial => "a partial def"
  | .thmInfo _ => "a theorem"
  | .opaqueInfo _ => "an opaque constant, as `partial def` and `opaque` declare"
  | .quotInfo _ => "a quotient primitive"
  | .inductInfo _ => "an inductive type"
  | .ctorInfo _ => "a constructor"
  | .recInfo _ => "a recursor"

def kindMatches (stated found : ConstantInfo) : Bool :=
  match stated, found with
  | .thmInfo _, .thmInfo _ => true
  | .defnInfo stated, .defnInfo found => stated.safety == found.safety
  | _, _ => false

def sameConstant (stated found : ConstantInfo) : Bool :=
  let value := fun (info : ConstantInfo) => (info.value? (allowOpaque := true)).map toShape
  stated.levelParams == found.levelParams && toShape stated.type == toShape found.type &&
    value stated == value found && match stated, found with
    | .defnInfo stated, .defnInfo found =>
      stated.safety == found.safety && stated.hints == found.hints && stated.all == found.all
    | .thmInfo stated, .thmInfo found => stated.all == found.all
    | .opaqueInfo stated, .opaqueInfo found => stated.isUnsafe == found.isUnsafe && stated.all == found.all
    | .axiomInfo stated, .axiomInfo found => stated.isUnsafe == found.isUnsafe
    | .inductInfo _, .inductInfo _ | .ctorInfo _, .ctorInfo _ | .recInfo _, .recInfo _
    | .quotInfo _, .quotInfo _ => true
    | _, _ => false

def standing (env : Environment) (moduleOf : Name → Option Name) (solutionImports : NameSet)
    (auxiliaries : Array ConstantInfo) (stated : ConstantInfo) : MetaM Standing := do
  let some found := env.find? stated.name | return .absent
  let some module := moduleOf stated.name | return .absent
  if !solutionImports.contains module then return .outside module
  if !kindMatches stated found then return .kind module (kindOf found)
  if stated.levelParams != found.levelParams then return .universes module found.levelParams
  if toShape stated.type != toShape found.type then
    let (plain, explicit) ← render found.type
    return .differs module plain explicit
  match auxiliaries.find? fun auxiliary => !((env.find? auxiliary.name).any (sameConstant auxiliary)) with
  | some auxiliary => return .auxiliary module auxiliary.name
  | none => return .holds module

structure Facts where
  inventory : Inventory := ⟨#[], #[]⟩
  blames : Array Blame := #[]
  challenge : Challenge := {}
  headlines : Array Headline := #[]
  holes : Array (Name × Option Name) := #[]
  registrations : Array (Name × Name × Option Role × Option Name) := #[]
  entry : Option (Option Name × Array Name) := none
  roots : Array Name := #[]
  challengeImports : Array Name := #[]
  terminations : Array Termination := #[]
  standings : Array (Name × Standing) := #[]
  cyclic : Array Name := #[]
  hidden : Array (String × String) := #[]
  solution : Name := .anonymous
  files : Array (Name × String) := #[]
  lines : Std.HashMap (Name × Name) Nat := {}
  written : Std.HashMap Name String := {}
  firstLines : Std.HashMap Name String := {}
  imports : Array (Name × Array (Name × Nat × String)) := #[]
  lints : Array (Name × Linter.LintEntry) := #[]
  specImports : Array (Name × Array ImportFact) := #[]
  noncomputableHoles : Array Name := #[]
  fixpoints : Array Name := #[]
  duplicates : Array (Name × Name × Name) := #[]
  parents : Std.HashMap Name Name := {}
  challengeFile : String := "Challenge.lean"

def Facts.fileOf (facts : Facts) (module : Name) : String :=
  if module == challengeModule then facts.challengeFile
  else ((facts.files.find? (·.1 == module)).map (·.2)).getD (toString module)

def Facts.lineOf (facts : Facts) (module name : Name) : Nat :=
  if module == challengeModule then facts.challenge.lineOf name else facts.lines.getD (module, name) 0

def Facts.place (facts : Facts) (module name : Name) : String :=
  let line := facts.lineOf module name
  if line == 0 then facts.fileOf module else s!"{facts.fileOf module}:{line}"

def Facts.settle (facts : Facts) (name : Name) : Name := Id.run do
  let mut current := name
  for _ in [0:name.getNumParts] do
    match facts.parents.get? current with
    | some parent => current := parent
    | none => break
  return current

def Facts.anchor (facts : Facts) (module name : Name) : Name := Id.run do
  let mut current := facts.settle (ownerOf (facts.settle name))
  for _ in [0:current.getNumParts] do
    if facts.lineOf module current != 0 then return current
    current := current.getPrefix
  return if facts.lineOf module (ownerOf name) != 0 then ownerOf name else name

def Facts.writtenOf (facts : Facts) (name : Name) : String :=
  facts.written.getD name (facts.challenge.writtenOf name)

def Facts.importLine (facts : Facts) (module dependency : Name) : Nat :=
  (((facts.imports.find? (·.1 == module)).bind fun (_, lines) => lines.find? (·.1 == dependency)).map (·.2.1)).getD 1

def Facts.importText (facts : Facts) (module dependency : Name) : String :=
  (((facts.imports.find? (·.1 == module)).bind fun (_, lines) => lines.find? (·.1 == dependency)).map
    (·.2.2)).getD s!"import {dependency}"

def Facts.codeFile (facts : Facts) : String :=
  ((facts.files.find? (Role.ofName ·.1 == .coreCode)).map (·.2)).getD "a CoreCode module"

private def lintNext : String := "then run `lake lint`"

private def buildNext : String := "then run `lake build`"

private def relockNext : String := "then delete owned.lock and run `lake build`"

private def ownerOnly (module : Name) : String :=
  s!"{module} is owned, so no edit to the editable files fixes it"

private def standardList : String := "propext, Classical.choice, and Quot.sound"

private def allowedImports : Role → String
  | .coreSpec => "only CoreSpec modules and modules outside the package"
  | .worldSpec => "only CoreSpec and WorldSpec modules and modules outside the package"
  | .coreCode => "only CoreSpec and CoreCode modules and modules outside the package"
  | .worldCode => "any module except tooling"
  | .tooling => "any module"

private def importPurpose : Role → String
  | .coreSpec => "the statements rest only on pure definitions"
  | .worldSpec => "claims about the world rest only on the statements' definitions"
  | .coreCode => "pure code never reaches foreign code or effects"
  | .worldCode => "the program never runs tooling"
  | .tooling => "nothing constrains it"

private def purity : Role → String
  | .coreSpec | .coreCode => "must be pure and total, so that the proofs are about the code that runs"
  | .worldSpec => "may declare foreign code only as `@[extern] opaque`, so that the kernel never unfolds it"
  | .worldCode => "may do IO but not use `unsafe`, `@[extern]`, or `@[implemented_by]`, so that the code that \
      runs is the code proved"
  | .tooling => "may do anything"

private def offence : String → String
  | "initializer" => "an initializer"
  | "IO" => "IO"
  | "dbg builtin" => "a dbg builtin"
  | reason => s!"`{reason}`"

private def cure (name : Name) : String → String
  | "unsafe" => s!"remove `unsafe` from {name}"
  | "partial" => s!"remove `partial` from {name} and recurse structurally or with `termination_by`"
  | "@[extern]" => s!"remove `@[extern]` from {name}, since only a WorldSpec module declares foreign code, as \
      `@[extern] opaque`"
  | "@[implemented_by]" => s!"remove `@[implemented_by]` from {name}"
  | "IO" => s!"move {name} to a WorldCode module"
  | "dbg builtin" => s!"remove the `dbg_trace` or `dbgTraceIfShared` call from {name}"
  | "@[extern] with a body the kernel unfolds" => s!"declare {name} as `@[extern \"…\"] opaque`, with no body"
  | reason => s!"remove {reason} from {name}"

private def located (project : Project) (module : Name) : String :=
  match project.role? module with
  | some role => s!"{module} ({role})"
  | none => s!"{module}, outside the package"

private def distinct (errors : Array String) : Array String :=
  errors.foldl (fun kept error => if kept.contains error then kept else kept.push error) #[]

private def within (space : Name) : String :=
  if space.isAnonymous then "" else s!", inside `namespace {space}`"

private def renamedInto (role : Role) (module : Name) : Name :=
  match module.components with
  | root :: rest@(_ :: _) => (root :: Name.mkSimple (toString role) :: rest).foldl (· ++ ·) .anonymous
  | _ => module ++ Name.mkSimple (toString role)

private def sourceFile (module : Name) : String :=
  "/".intercalate (module.components.map toString) ++ ".lean"

private def isInitializer (name : Name) : Bool :=
  (privateToUserName name).components.contains `initFn

def Facts.programFile? (facts : Facts) : Option String :=
  let roots := if facts.roots.isEmpty then (facts.files.filter (Role.ofName ·.1 == .worldCode)).map (·.1)
    else facts.roots
  match roots with
  | #[root] => some (facts.fileOf root)
  | _ => none

def Facts.worldFile (facts : Facts) : String :=
  ((facts.files.find? (Role.ofName ·.1 == .worldCode)).map (·.2)).getD "a WorldCode module"

private structure Fault where
  own : String
  whose : String
  fix : String

private def faultOf (axiomName culprit : Name) (nativePlace : String) : Fault :=
  if axiomName == ``sorryAx then
    { own := s!"{culprit} uses `sorry`, so it is not proved"
      whose := "whose proof uses `sorry`"
      fix := s!"Replace each `sorry` in {culprit} with a proof or a definition" }
  else match nativeTactic? axiomName with
    | some tactic =>
      let replacement := if tactic == `native_decide then "`decide`" else "a proof the kernel checks, such as `decide`"
      { own := s!"{culprit} is proved with `{tactic}`, which asserts the evaluated result as an axiom, but the \
          comparator permits only {standardList}, so the proof is not checked"
        whose := s!"which is proved with `{tactic}`, whose axiom the comparator does not permit"
        fix := s!"Replace `{tactic}` at {nativePlace} with {replacement}" }
    | none =>
      let shown := privateToUserName axiomName
      { own := s!"{culprit} depends on axiom {shown}, but the comparator permits only {standardList}, so its proof \
          is not checked"
        whose := s!"which depends on axiom {shown}"
        fix := s!"Prove {culprit} without {shown}" }

def axiomErrors (facts : Facts) (owner : Bool := false) : Array String := Id.run do
  let moduleOf := fun (name : Name) => (facts.inventory.declarations.find? (·.name == name)).map (·.moduleName)
  let placeOf := fun (name : Name) => (moduleOf name).map fun module => facts.place module (facts.anchor module name)
  let targets := facts.challenge.declared.map (·.name)
  let close := fun (module : Name) (fix : String) =>
    if owner then s!", and {ownerOnly module}. {fix} in {facts.fileOf module}, {relockNext}."
    else s!". {fix}, {lintNext}."
  let mut errors := #[]
  for blame in facts.blames do
    let place := facts.place blame.module (facts.anchor blame.module blame.declaration)
    let shown := privateToUserName (ownerOf blame.declaration)
    if blame.axiomName == blame.declaration then
      if (nativeTactic? blame.axiomName).isNone then
        let fix := if owner then s!"Delete `axiom {shown}`, and state it as a headline of {facts.challengeFile} or \
            as a WorldClaim in a WorldSpec module"
          else s!"Delete `axiom {shown}` and prove what uses it"
        errors := errors.push s!"{place}: `axiom {shown}` asserts {shown} without proof, but the comparator \
          permits only {standardList}{close blame.module fix}"
      continue
    let culprit := privateToUserName (ownerOf blame.culprit)
    let nativePlace := ((moduleOf blame.axiomName).map (facts.place · blame.axiomName)).getD place
    let fault := faultOf blame.axiomName culprit nativePlace
    if culprit == shown then
      errors := errors.push s!"{place}: {fault.own}{close blame.module fault.fix}"
    else if owner then
      continue
    else if let some culpritPlace := placeOf blame.culprit then
      if targets.contains shown then
        errors := errors.push s!"{place}: {shown} is not proved, because it uses {culprit} ({culpritPlace}), \
          {fault.whose}. {fault.fix}, {lintNext}."
    else
      let source := (blame.culpritModule.map toString).getD "a module"
      errors := errors.push s!"{place}: {shown} uses {culprit}, which {source} declares outside the package, \
        {fault.whose}, so the proof of {shown} is not checked. Prove {shown} without {culprit}, {lintNext}."
  return errors

def isSpec (project : Project) (module : Name) : Bool :=
  (project.role? module) matches some .coreSpec | some .worldSpec

def offenceGroups (project : Project) (facts : Facts) (spec : Bool) : Array (Name × Name × Role × List String) :=
  Id.run do
    let mut groups : Array (Name × Name × Role × List String) := #[]
    for fact in facts.inventory.declarations do
      let some role := project.role? fact.moduleName | continue
      unless isSpec project fact.moduleName == spec do continue
      let reasons := fact.reasons role
      if reasons.isEmpty then continue
      let anchor := facts.anchor fact.moduleName fact.name
      match groups.findIdx? fun (module, name, _, _) => module == fact.moduleName && name == anchor with
      | some index => groups := groups.modify index fun (module, name, role, known) =>
          (module, name, role, known ++ reasons.filter (!known.contains ·))
      | none => groups := groups.push (fact.moduleName, anchor, role, reasons)
    return groups

def offenceErrors (project : Project) (facts : Facts) (owner : Bool) : Array String := Id.run do
  let mut errors := #[]
  let groups := offenceGroups project facts owner
  let named := groups.filterMap fun (module, anchor, _, _) =>
    if anchor.hasMacroScopes then none else some (facts.place module anchor)
  for (module, anchor, role, reasons) in groups do
    let place := facts.place module anchor
    if anchor.hasMacroScopes && named.contains place then continue
    let shown := privateToUserName (ownerOf anchor)
    let site := located project module
    let close := if owner then s!", and {ownerOnly module}" else ""
    let next := if owner then s!"in {facts.fileOf module}, {relockNext}" else lintNext
    let initializes := isInitializer anchor || facts.inventory.declarations.any fun fact =>
      fact.moduleName == module && isInitializer fact.name && facts.anchor module fact.name == anchor
    if reasons.contains "initializer" || initializes then
      let quoted := facts.firstLines.getD anchor s!"initialize {shown}"
      let others := reasons.filter fun reason => reason != "initializer" && reason != "IO"
      let also := if others.isEmpty then "" else s!", and {" and ".intercalate (others.map (cure shown))}"
      errors := errors.push s!"{place}: `{quoted}` runs IO when the program starts, in {site}, but {role} code \
        {purity role}{close}. Move it to a WorldCode module{also}, {next}."
    else
      errors := errors.push s!"{place}: {shown} uses {" and ".intercalate (reasons.map offence)} in {site}, but \
        {role} code {purity role}{close}. {(" and ".intercalate (reasons.map (cure shown))).capitalize}, {next}."
  return errors

def sound (project : Project) (facts : Facts) : Array String := Id.run do
  let mut errors := #[]
  for fact in facts.inventory.modules do
    if isSpec project fact.name then continue
    let file := facts.fileOf fact.name
    let some role := project.role? fact.name
      | errors := errors.push s!"{file}: no lean_lib of the package builds {fact.name}, so the audit gives it no \
          role. Build it from a lean_lib in lakefile.lean; lakefile.lean is owned, so delete owned.lock and run \
          `lake build` to record it, {lintNext}."
    unless fact.usesModuleSystem do
      errors := errors.push s!"{file}:1: {fact.name} does not start with `module`, so the audit cannot tell what \
        it exposes. Add `module` as the first line of {file}, {lintNext}."
    for dependency in fact.imports do
      unless project.admits role dependency do
        let line := facts.importLine fact.name dependency.name
        let fix := if project.role? dependency.name == some .tooling && (role == .coreCode || role == .worldCode) then
            let renamed := renamedInto .coreCode dependency.name
            let kinds := if role == .coreCode then "a CoreCode module" else "a CoreCode or WorldCode module"
            s!"Rename {dependency.name} to {kinds}, as in {renamed} ({sourceFile renamed}), and update line {line} \
              of {file}"
          else if role == .coreSpec || role == .worldSpec then
            s!"Delete line {line}, `{facts.importText fact.name dependency.name}`, from {file}, which is owned, so \
              then delete owned.lock and run `lake build`"
          else s!"Delete line {line}, `{facts.importText fact.name dependency.name}`, from {file}"
        let how := if dependency.comptime then "meta-imports" else "imports"
        errors := errors.push s!"{file}:{line}: {fact.name} ({role}) {how} {located project dependency.name}, \
          but {role} may import {allowedImports role}, so that {importPurpose role}. {fix}, {lintNext}."
  errors := errors ++ axiomErrors { facts with blames := facts.blames.filter (!isSpec project ·.module) } ++
    offenceErrors project facts false
  for (hole, module) in facts.holes do
    if let some module := module then
      unless (project.role? module) matches some .coreCode | some .worldCode do
        errors := errors.push s!"{facts.place module hole}: hole {hole} is defined in {located project module}, \
          but a hole is code, which lives in CoreCode or WorldCode, where the audit checks what it may do. Move \
          `def {facts.writtenOf hole}` from {facts.fileOf module} to {facts.codeFile}, or to a WorldCode module if \
          it does IO{within (facts.challenge.namespaceOf hole)}, {lintNext}."
  for hole in facts.noncomputableHoles do
    if let some (_, some module) := facts.holes.find? (·.1 == hole) then
      errors := errors.push s!"{facts.place module hole}: hole {hole} is `noncomputable` in {module}, so no code \
        runs it, and the headlines about it say nothing about a program. Define {hole} without `noncomputable` in \
        {facts.fileOf module}, {lintNext}."
  for hole in facts.fixpoints do
    if let some (_, some module) := facts.holes.find? (·.1 == hole) then
      if project.role? module == some .worldCode && !facts.terminations.any (·.definition == hole) then
        errors := errors.push s!"{facts.place module hole}: hole {hole} is defined with `partial_fixpoint` in \
          {module}, so it may not return, but no headline of {facts.challengeFile} is marked \
          `@[terminates {hole}]` to state on which inputs it does, so a headline about {hole} could hold while \
          the program never returns. Define {hole} by structural recursion or with `termination_by`, without \
          `partial_fixpoint`, in {facts.fileOf module}, {lintNext}."
  for (name, kept, dropped) in facts.duplicates do
    errors := errors.push s!"{facts.place dropped name}: {name} is declared in both {dropped} and {kept} \
      ({facts.place kept name}), and Lean keeps only the one it imports first, so the audit and the comparator \
      never check the one in {dropped}. Rename or delete {name} in {facts.fileOf dropped}, {lintNext}."
  if let some (some module, _) := facts.entry then
    unless (project.role? module) matches some .worldCode do
      if facts.roots.contains module then
        let moved := renamedInto .worldCode module
        errors := errors.push s!"{facts.place module `main}: main is defined in {located project module}, the root \
          of the package's lean_exe, but main runs the program, which does IO, and only WorldCode may. In \
          lakefile.lean, set that lean_exe's `root` to a WorldCode module, such as {moved}, and move \
          {facts.fileOf module} to {sourceFile moved}; lakefile.lean is owned, so then delete owned.lock and run \
          `lake build`, {lintNext}."
      else
        let program := (facts.programFile?).getD "the WorldCode module that is the root of the lean_exe"
        errors := errors.push s!"{facts.place module `main}: main is defined in {located project module}, but main \
          runs the program, which does IO, and only WorldCode may. Move `def main` from {facts.fileOf module} to \
          {program}, outside any namespace, {lintNext}."
  for t in facts.terminations do
    if let some (_, some module) := facts.holes.find? (·.1 == t.definition) then
      unless t.fixpoint do
        errors := errors.push s!"{facts.place module t.definition}: hole {t.definition} is not defined with \
          `partial_fixpoint`, but `@[terminates {t.definition}]` on {t.headline} \
          ({facts.place challengeModule t.headline}) admits it only as a partial_fixpoint definition, whose \
          termination {t.headline} states. Define {t.definition} with `partial_fixpoint` after its body in \
          {facts.fileOf module}, {lintNext}."
  return distinct errors

def warned (facts : Facts) : Array String :=
  facts.lints.map fun (module, entry) =>
    let file := facts.fileOf module
    let line := (entry.position?.getD entry.message.pos).line
    let said := (((entry.message.data.splitOn "\n").map (·.trimAscii.toString)).find? (!·.isEmpty)).getD ""
    s!"{file}:{line}: Lean's linter {entry.linter} reports \"{said}\", so {module} does not pass Lean's linters, \
      which `lake lint` requires of every module the default targets build. Change line {line} of {file} as the warning says, \
      {lintNext}."

def registered (project : Project) (facts : Facts) : Array String := Id.run do
  let mut errors := #[]
  for (claim, module, role, home) in facts.registrations do
    if isSpec project module then continue
    let file := facts.fileOf module
    if home != some module then
      let declared := match home with
        | some home => s!", declared at {facts.place home claim},"
        | none => ""
      errors := errors.push s!"{file}: {module} adds {claim}{declared} to the world claims without the \
        `WorldClaim` command, so headlines could assume it as a checked claim. Delete the command in {file} that \
        calls `SoftwareChallenge.claimsExt.addEntry`, {lintNext}."
    else if role != some .worldSpec then
      errors := errors.push s!"{facts.place module claim}: WorldClaim {claim} is declared in \
        {located project module}, but a world claim is an assumption about the world, which only a WorldSpec \
        module states. Remove the `WorldClaim {facts.writtenOf claim}` command and its doc comment from {file}, \
        {lintNext}."
  return errors

def ownedViolations (project : Project) (facts : Facts) (imports : Bool) : Array String := Id.run do
  let mut errors := #[]
  for fact in facts.inventory.modules do
    let some role := project.role? fact.name | continue
    unless isSpec project fact.name do continue
    let file := facts.fileOf fact.name
    unless fact.usesModuleSystem do
      errors := errors.push s!"{file}:1: {fact.name} does not start with `module`, so the audit cannot tell what \
        it exposes, and {ownerOnly fact.name}. Add `module` as the first line of {file}, {relockNext}."
    if imports then
      for dependency in fact.imports do
        unless project.admits role dependency do
          let line := facts.importLine fact.name dependency.name
          let how := if dependency.comptime then "meta-imports" else "imports"
          errors := errors.push s!"{file}:{line}: {fact.name} ({role}) {how} {located project dependency.name}, \
            but {role} may import {allowedImports role}, so that {importPurpose role}, and {ownerOnly fact.name}. \
            Delete line {line}, `{facts.importText fact.name dependency.name}`, from {file}, {relockNext}."
  errors := errors ++ offenceErrors project facts true ++
    axiomErrors { facts with blames := facts.blames.filter (isSpec project ·.module) } (owner := true)
  for (claim, module, role, home) in facts.registrations do
    unless isSpec project module do continue
    let file := facts.fileOf module
    if home != some module then
      errors := errors.push s!"{file}: {module} adds {claim} to the world claims without the `WorldClaim` command, \
        so headlines could assume it as a checked claim, and {ownerOnly module}. Delete the command in {file} that \
        calls `SoftwareChallenge.claimsExt.addEntry`, {relockNext}."
    else if role != some .worldSpec then
      errors := errors.push s!"{facts.place module claim}: WorldClaim {claim} is declared in \
        {located project module}, but a world claim is an assumption about the world, which only a WorldSpec \
        module states, and {ownerOnly module}. Move the `WorldClaim {facts.writtenOf claim}` command and its doc \
        comment from {file} to a WorldSpec module, {relockNext}."
  return distinct errors

def evidenced (facts : Facts) : Array String :=
  facts.headlines.filterMap fun line => line.unlinted.map fun module =>
    s!"{facts.place module line.name}: {line.name} is proved in {module}, which does not run the premise linter, \
      so the report cannot tell which world claims the proof uses. Add `meta import SoftwareChallenge` to \
      {facts.fileOf module}, {lintNext}."

def meaningful (facts : Facts) : Array String :=
  let challenge := facts.challenge
  let file := facts.challengeFile
  let here := fun (name : Name) => facts.place challengeModule name
  let written := fun (name : Name) => challenge.writtenOf name
  let stated := challenge.headlines.filterMap fun name => (challenge.statement? name).map (name, toShape ·)
  let mentioned := NameSet.ofList <| (challenge.headlines.flatMap fun name =>
    ((challenge.statement? name).map (·.getUsedConstants)).getD #[]).toList
  let duplicates := (stated.mapIdx fun index (later, shape) =>
    ((stated.extract 0 index).find? (·.2 == shape)).map fun (earlier, _) => (later, earlier)).filterMap id
  let unreproducible := challenge.auxiliaries.filterMap fun (name, auxiliaries) =>
    if auxiliaries.any (isPrivateName ·.name) then some name else none
  let settled := fun (name : Name) => duplicates.any (·.1 == name) || unreproducible.contains name
  let candidates := ", ".intercalate (challenge.headlines.map written).toList
  let applicable := challenge.preconditioned.filterMap fun preconditions =>
    preconditions.mentions.map fun _ => written preconditions.headline
  let templateOf := fun (name : Name) =>
    ((challenge.templates.find? (·.1 == name)).map (·.2)).getD s!"¬ ({(challenge.renderedOf name).1})"
  let replacedIn := fun (name : Name) =>
    let holes := ((challenge.statement? name).map fun statement =>
      statement.getUsedConstants.filter challenge.holes.contains).getD #[]
    if holes.isEmpty then "each foreign function it mentions" else " and ".intercalate (holes.map toString).toList
  (duplicates.map fun (later, earlier) =>
    s!"{here later}: {later} states the same as {earlier} ({here earlier}), up to binder names, so it claims \
      nothing new. Remove {later} and its kills and witnesses from {file}, {buildNext}.") ++
  ((challenge.fixed.filter (!settled ·)).map fun headline =>
    s!"{here headline}: {headline} mentions no hole or foreign function, so no implementation can make it false, \
      and no kill can show that it rejects one. State it about a hole, or move it to a CoreSpec module as a \
      lemma, {buildNext}.") ++
  (challenge.headlines.filterMap fun headline =>
    if settled headline || challenge.fixed.contains headline || !(challenge.killsOf headline).isEmpty ||
      challenge.unmarked.any (·.1 == headline) then none
    else match challenge.unmarked.find? (·.2 == headline) with
      | some (kill, _) => some s!"{here headline}: {headline} has no kill, so nothing shows it rejects a wrong \
          implementation, but {kill} ({here kill}) states one. Mark {kill} `@[kills {written headline}]` in {file}, \
          {buildNext}."
      | none => some s!"{here headline}: {headline} has no kill, so nothing shows it rejects a wrong \
          implementation. Add `@[kills {written headline}] theorem {lastOf headline}_rejects : \
          {templateOf headline} := by sorry` to {file}{within (challenge.namespaceOf headline)}, and replace each \
          `?wrong_…` in it with a wrong implementation of that hole, {buildNext}.") ++
  ((challenge.misshapen.filter fun (_, headline) => !settled headline && !challenge.fixed.contains headline).map
    fun (kill, headline) =>
    if !challenge.headlines.contains headline then s!"{here kill}: {kill} is marked `@[kills {headline}]`, but \
      {headline} is not a headline of {file}, so the kill rejects nothing claimed. Name in `@[kills …]` the \
      headline it rejects, one of {candidates}, or delete {kill} from {file}, {buildNext}."
    else if challenge.unreplaced.contains (kill, headline) then s!"{here kill}: {kill} is `¬` {headline} with no \
      hole replaced, so it says that {headline} is false and can never be proved. Replace {replacedIn headline} \
      in it with a wrong implementation, {buildNext}."
    else s!"{here kill}: {kill} is marked `@[kills {headline}]`, but it is neither `¬` {headline} with its holes \
      and WorldSpec foreign functions replaced by wrong implementations, nor that negation `∧` every other headline \
      in {file} order under the same replacement, so it does not show that {headline} rejects anything. Restate \
      {kill} as `{templateOf headline}`, with each `?wrong_…` replaced by a wrong implementation of that hole, or \
      name in `@[kills …]` the headline it rejects, {buildNext}.") ++
  (challenge.preconditioned.filterMap fun preconditions => preconditions.mentions.bind fun constant =>
    let what := if preconditions.inInput then "the type of an input" else "a precondition"
    if !(challenge.witnessesOf preconditions.headline).isEmpty then none
    else some s!"{here preconditions.headline}: {what} of {preconditions.headline} mentions {constant}, so no \
      kill shows that some input meets it, and {preconditions.headline} could hold vacuously. Add \
      `@[witness {written preconditions.headline}] theorem {lastOf preconditions.headline}_applies : \
      {preconditions.expected} := by sorry` to {file}{within (challenge.namespaceOf preconditions.headline)}, \
      {buildNext}.") ++
  (challenge.misshapenWitnesses.map fun (witness, headline) =>
    let marked := s!"{here witness}: {witness} is marked `@[witness {headline}]`, but"
    match challenge.preconditioned.find? (·.headline == headline) with
    | some preconditions => s!"{marked} it is not `{preconditions.expected}`: the world claims of {headline} that \
        mention no input, then `∃` the inputs its preconditions use, in order, of their conjunction, with holes \
        kept, so it does not show that some input meets them. Restate {witness} as `{preconditions.expected}`, \
        {buildNext}."
    | none => if challenge.headlines.contains headline then s!"{marked} {headline} has no precondition to meet, \
        so the witness shows nothing. Remove {witness} from {file}, {buildNext}."
      else if applicable.isEmpty then s!"{marked} {headline} is not a headline of {file}, and no headline has a \
        precondition that mentions a hole or a foreign function, so the witness shows nothing. Remove {witness} \
        from {file}, {buildNext}."
      else s!"{marked} {headline} is not a headline of {file}, so the witness meets no claimed precondition. \
        Name in `@[witness …]` the headline whose preconditions it meets, one of \
        {", ".intercalate applicable.toList}, or delete {witness} from {file}, {buildNext}.") ++
  (challenge.holes.filter (!mentioned.contains ·)).map fun hole =>
    s!"{here hole}: no headline mentions hole {hole}, so nothing is claimed about it. State a headline about \
      {hole} in {file}, or remove the hole, {buildNext}."

def owned (project : Project) (facts : Facts) : Array String := Id.run do
  let file := facts.challengeFile
  let mut errors := #[]
  for dependency in facts.challengeImports do
    unless project.admits .worldSpec { name := dependency, comptime := false } do
      let line := facts.importLine challengeModule dependency
      errors := errors.push s!"{file}:{line}: {challengeModule} imports {located project dependency}, but a \
        challenge may import only CoreSpec and WorldSpec modules and modules outside the package, so that the \
        statement rests only on what its owner wrote. Delete line {line}, \
        `{facts.importText challengeModule dependency}`, from {file}, and import the CoreSpec or WorldSpec modules \
        it needs instead, {buildNext}."
  for name in facts.challenge.filled do
    errors := errors.push s!"{facts.place challengeModule name}: {challengeModule} defines {name} with a body, but \
      a challenge declares only theorems and holes, which the solution implements. Make {name} a hole with \
      `:= sorry`, or move it to a CoreSpec module, {buildNext}."
  for name in facts.challenge.axioms do
    errors := errors.push s!"{facts.place challengeModule name}: `axiom {name}` asserts {name} without proof, but a \
      challenge declares only theorems and holes, and the comparator permits no axiom of the challenge. Delete \
      `axiom {name}`, and state it as a headline to prove, or as a WorldClaim in a WorldSpec module if it is an \
      assumption about the world, {buildNext}."
  for (name, line) in facts.challenge.privates do
    let shown := privateToUserName name
    errors := errors.push s!"{file}:{line}: {shown} is `private`, so the comparator and the audit cannot see it, and \
      nothing claims it. Remove `private` from {shown} at {file}:{line}, {buildNext}."
  for (name, module, line) in facts.challenge.derivedPartials do
    let moduleFile := facts.fileOf module
    let place := (line.map (s!"{moduleFile}:{·}")).getD moduleFile
    let role := (project.role? module).getD .coreSpec
    errors := errors.push s!"{place}: `deriving` makes {name} a `partial` definition in {module} ({role}), because \
      its type is nested or mutual, so no proof can unfold it, and a statement that uses it cannot be proved about \
      the code. Write that instance by structural recursion in {moduleFile}, or remove the `deriving` clause; then \
      delete owned.lock and run `lake build`."
  for (module, imports) in facts.specImports do
    let some role := project.role? module | continue
    let moduleFile := facts.fileOf module
    for dependency in imports do
      unless project.admits role dependency do
        let line := facts.importLine module dependency.name
        let how := if dependency.comptime then "meta-imports" else "imports"
        errors := errors.push s!"{moduleFile}:{line}: {module} ({role}) {how} {located project dependency.name}, \
          but {role} may import {allowedImports role}, with `meta import` too, so that the statement rests only on \
          owned files: a solution may edit {dependency.name}, and with it the statement, while owned.lock stays \
          the same. Move what {module} uses from {dependency.name} into a CoreSpec module and delete line {line}, \
          `{facts.importText module dependency.name}`, from {moduleFile}; then delete owned.lock and run `lake build`."
  return errors

def stated (facts : Facts) : Array String := Id.run do
  let challenge := facts.challenge
  let file := facts.challengeFile
  let here := fun (name : Name) => facts.place challengeModule name
  let mut errors := #[]
  for t in facts.terminations do
    let marked := s!"{here t.headline}: `@[terminates {t.definition}]` on {t.headline}"
    unless challenge.holes.contains t.definition do
      errors := errors.push s!"{marked} names {t.definition}, which is not a hole of {file}, so no headline \
        speaks about its termination. Name a hole declared with `:= sorry` in {file}, or remove the attribute, \
        {buildNext}."
    unless challenge.headlines.contains t.headline && !(challenge.killsOf t.headline).isEmpty do
      errors := errors.push s!"{marked}: {t.headline} is not a headline with a kill, so nothing shows that it \
        rejects a diverging implementation. Move the attribute to a headline with a kill, {buildNext}."
    unless t.mentioned do
      errors := errors.push s!"{marked}: {t.headline} does not mention {t.definition}, so it cannot state on \
        which inputs {t.definition} returns. Move the attribute to a headline that does, {buildNext}."
  for (name, hypotheses) in challenge.aboutHoles do
    for (hypothesis, hole) in hypotheses do
      errors := errors.push s!"{here name}: {name} assumes `{hypothesis}`, which is about hole {hole}, so the \
        solution decides whether it holds, and when it does not, {name} holds vacuously. Remove the hypothesis, or \
        state it as its own headline, with a kill, {buildNext}."
  for (name, hypotheses) in challenge.hypotheses do
    for hypothesis in hypotheses do
      errors := errors.push s!"{here name}: {name} assumes `{hypothesis}`, which is not a WorldClaim, so no Check \
        tests it, and a false assumption would make {name} vacuous. Declare it in a WorldSpec module as \
        `WorldClaim Name := {hypothesis}`, with a doc comment, and assume that, or remove the hypothesis, \
        {buildNext}."
  for (name, auxiliaries) in challenge.auxiliaries do
    for auxiliary in auxiliaries.filter (isPrivateName ·.name) do
      errors := errors.push s!"{here name}: the statement of {name} elaborates to the private constant \
        {privateToUserName auxiliary.name}, which no solution can reproduce, so {name} can never be proved. \
        Write that part of the statement as a term, without tactics or `decide`, {buildNext}."
  return errors

def ownedReason (challengeFile file : String) : String :=
  if file == "lakefile.lean" then "it configures how the package builds and how lint judges it"
  else if file == "lake-manifest.json" then "it pins the dependencies that build and check the statement"
  else if file == "lean-toolchain" then "it fixes the Lean version that checks the statement"
  else if file == challengeFile then "it states the challenge"
  else "a component of its module name is CoreSpec or WorldSpec, so it is part of the statement"

def restoreCommand (file : String) : String :=
  s!"git checkout $(git log -1 --format=%H -- owned.lock) -- {file}"

def lockErrors (locked current : Array (String × UInt64)) (edit : Array String) (challengeFile : String)
    (next : String := "lake lint") : Array String :=
  let editable := if edit.isEmpty then "the CoreCode and WorldCode modules" else ", ".intercalate edit.toList
  let configuration := ["lakefile.lean", "lake-manifest.json", "lean-toolchain", challengeFile]
  (current.filterMap fun (file, digest) => match locked.find? (·.1 == file) with
    | none => some <| if configuration.contains file then
        s!"{file} is owned, because {ownedReason challengeFile file}, but owned.lock does not record it, so a \
          change to it would go unreviewed. Delete owned.lock and run `lake build` to record it, then run `{next}`."
      else s!"{file} is owned, because {ownedReason challengeFile file}, but owned.lock does not record it, so it \
          would change the statement unreviewed. Remove or rename {file}; to add it to the statement, delete \
          owned.lock and run `lake build` to record it. Then run `{next}`."
    | some (_, recorded) => if recorded == digest then none
      else some s!"{file} differs from owned.lock, but {ownedReason challengeFile file}, which a solution must not \
        change. Restore it with `{restoreCommand file}` and edit {editable} instead; to change the statement, \
        delete owned.lock and run `lake build` to record it. Then run `{next}`.") ++
  (locked.filter fun (file, _) => !current.any (·.1 == file)).map fun (file, _) =>
    s!"{file} is recorded in owned.lock but missing, and {ownedReason challengeFile file}, which a solution must \
      not change. Restore it with `{restoreCommand file}`; to drop it from the statement, delete owned.lock and run \
      `lake build` to record it. Then run `{next}`."

def statementTarget : String :=
  "@[default_target]\ntarget statement pkg : Unit := do\n  \
    return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())"

private def difference (expected found : String) : String :=
  let field := fun (text key : String) => (Json.parse text).toOption.bind fun json => (json.getObjVal? key).toOption
  let names := fun (text : String) => ["theorem_names", "definition_names"].toArray.flatMap fun key =>
    ((field text key).bind fun json => (fromJson? json : Except String (Array String)).toOption).getD #[]
  let declared := names expected
  let listed := names found
  let gone := listed.filter (!declared.contains ·)
  let added := declared.filter (!listed.contains ·)
  let module := fun (text : String) => (field text "solution_module").map (·.compress)
  let parts := (if gone.isEmpty then [] else
      [s!"it lists {", ".intercalate gone.toList}, which Challenge.lean no longer declares"]) ++
    (if added.isEmpty then [] else [s!"it omits {", ".intercalate added.toList}, which Challenge.lean declares"]) ++
    if module expected == module found then [] else
      [s!"it names the solution module {(module found).getD "null"}, but the package's is {(module expected).getD "null"}"]
  if parts.isEmpty then "its contents differ from what `lake build` writes" else "; ".intercalate parts

def noTargetError : String :=
  s!"lakefile.lean has no `statement` target, so `lake build` neither records owned.lock nor writes \
    comparator.json. Add these lines to lakefile.lean, delete owned.lock if it exists, and run `lake build` to \
    record lakefile.lean and write comparator.json, {lintNext}:\n\n{statementTarget}\n"

def comparatorErrors (expected : String) (existing : Option String) (target : Bool) : Array String :=
  match existing with
  | none => if target then
      #[s!"comparator.json is missing: `lake build` writes it from Challenge.lean, and has not written it here \
        yet. Run `lake build`, {lintNext}."]
    else #[noTargetError]
  | some text => if text == expected then #[] else
      #[s!"comparator.json does not match Challenge.lean: {difference expected text}. Run `lake build` to \
        regenerate it, {lintNext}."]

def pending (facts : Facts) : Array String := Id.run do
  let challenge := facts.challenge
  let here := fun (name : Name) => facts.place challengeModule name
  let solution := facts.solution
  let solutionFile := facts.fileOf solution
  let mut items := #[]
  for (name, standing) in facts.standings do
    let hole := challenge.holes.contains name
    let what := if hole then s!"hole {name}" else toString name
    let signature := challenge.signatureOf name
    let space := within (challenge.namespaceOf name)
    match standing with
    | .holds _ | .unsound _ => pure ()
    | .absent =>
      items := items.push <| if hole then
        s!"{here name}: hole {name} is not implemented yet, {challenge.purpose name}. Add `{signature} := …` to \
          {facts.codeFile}, or to a WorldCode module if it does IO{space}, {lintNext}."
      else s!"{here name}: {name} is not proved yet, {challenge.purpose name}. Add `{signature} := …`, with a \
          proof, to {solutionFile}{space}, {lintNext}."
    | .outside module =>
      let file := facts.fileOf module
      items := items.push <| if facts.cyclic.contains module then
        s!"{facts.place module name}: {what} is in {module}, which imports {solution}, so {solution} cannot \
          import it back, and the comparator reads only {solution} and its imports. Move \
          `{challenge.keywordOf name} {facts.writtenOf name}` from {file} into {solutionFile}{space}, {lintNext}."
      else s!"{facts.place module name}: {what} is in {module}, which {solution} does not import, so the \
          comparator, which reads only {solution} and its imports, cannot see it. Add `public import {module}` to \
          the imports of {solutionFile}, or move {name} into {solutionFile}, {lintNext}."
    | .kind module found =>
      items := items.push <| if hole then
        s!"{facts.place module name}: hole {name} is {found} in {module}, but {here name} declares a `def`, so the \
          comparator rejects it. Define it with `def`, without `partial`, `unsafe`, or `opaque`, in \
          {facts.fileOf module}, {lintNext}."
      else s!"{facts.place module name}: {name} is {found} in {module}, but {here name} states it as a theorem, so \
          the comparator rejects it. Declare it with `theorem` in {facts.fileOf module}, {lintNext}."
    | .universes module found =>
      let shown := fun (levels : List Name) => if levels.isEmpty then "none" else ", ".intercalate (levels.map toString)
      let expected := ((challenge.declared.find? (·.name == name)).map (·.levelParams)).getD []
      items := items.push s!"{facts.place module name}: {what} has universe parameters {shown found} in {module}, but \
        {shown expected} in {here name}, so the comparator rejects it. Declare it with the universe parameters \
        of {here name}, in that order, {lintNext}."
    | .differs module plain explicit =>
      let (statedPlain, statedExplicit) := challenge.renderedOf name
      let (found, expected) := if plain == statedPlain then (explicit, statedExplicit) else (plain, statedPlain)
      items := items.push s!"{facts.place module name}: {what} {if hole then "has type" else "states"} `{found}` in \
        {module}, but `{expected}` in {here name}, so the comparator rejects it. Restate it as `{signature} := …`, \
        {lintNext}."
    | .auxiliary module constant =>
      items := items.push s!"{facts.place module name}: {what} elaborates to {constant} in {module}, which differs \
        from the {constant} that {here name} elaborates to, so the comparator rejects it. Copy the statement of \
        {name} from {here name} verbatim, {lintNext}."
  match facts.entry with
  | some (none, _) =>
    let calls := if challenge.holes.isEmpty then ""
      else s!", calling {" and ".intercalate (challenge.holes.map toString).toList}"
    let unbuilt := facts.roots.filter fun root => !facts.files.any (·.1 == root)
    items := items.push <| if !unbuilt.isEmpty then
        let root := unbuilt[0]!
        s!"lakefile.lean: {root} is the root of the package's lean_exe, but no default target builds it, so the \
          audit cannot see main. In lakefile.lean, mark that lean_exe `@[default_target]`, or add {root} to the \
          globs of the default lean_lib; lakefile.lean is owned, so then delete owned.lock and run `lake build`, \
          {lintNext}."
      else match facts.programFile? with
      | some file => s!"{file}: main is not written yet, but the package declares a lean_exe, and the audit \
          checks that main reaches every hole. Add `def main : IO Unit := …` at the end of {file}, outside any \
          namespace{calls}, {lintNext}."
      | none => s!"main is not written yet, but the package declares a lean_exe, and the audit checks that main \
          reaches every hole. Add `def main : IO Unit := …` at the end of the WorldCode module that is the root of \
          the lean_exe, outside any namespace{calls}, {lintNext}."
  | some (some module, unreached) =>
    let absent := fun (hole : Name) =>
      facts.standings.any fun (name, standing) => name == hole && standing matches .absent
    for hole in unreached.filter (!absent ·) do
      items := items.push s!"{here hole}: hole {hole} is never called from main, so the headlines about it say \
        nothing about the program that runs. Call {hole} from main ({facts.place module `main}), or from code main \
        runs, {lintNext}."
  | none => pure ()
  for line in facts.headlines do
    for unmatched in line.unmatched do
      let module := (unmatched.module.map facts.fileOf).getD "an unknown module"
      items := items.push s!"{module}:{unmatched.line}: this Check cannot be matched against {unmatched.premise}, \
        which {line.name} assumes, within the audit's budget of {matchBudget} heartbeats, so it does not count as \
        a Check of it. Restate that Check with the arguments of the premise, as `Check {unmatched.premise} …`, \
        {lintNext}."
    for assumption in line.assumptions.filter (·.checks == 0) do
      let chosen := if assumption.checkVariables.isEmpty then ""
        else s!", with a value of your choice in place of {" and ".intercalate assumption.checkVariables.toList}"
      items := items.push s!"{here line.name}: {line.name} assumes the world claim {assumption.statement}, which no \
        Check tests against the real foreign code. Add `Check {assumption.checkStatement} := do …`, or \
        `Check {assumption.checkStatement} : <an instance it implies>`, to {facts.worldFile}{chosen}, {lintNext}."
  for (name, dir) in facts.hidden do
    items := items.push s!"lakefile.lean: the comparator's sandbox hides package {name} at {dir}, because it mounts \
      empty directories over /home, /root, /run, /tmp, and /var, so `lake comparator` cannot build the solution. \
      lakefile.lean and lake-manifest.json are owned, so the fix records a new statement: in lakefile.lean, \
      require {name} from git, so that it lives in .lake/packages, or from a directory outside those, run \
      `lake update {name}`, delete owned.lock, and run `lake build` to record them, {lintNext}."
  return items

def importLines (file : System.FilePath) : IO (Array (Name × Nat × String)) := do
  return ((← IO.FS.readFile file).splitOn "\n").toArray.zipIdx.filterMap fun (line, index) =>
    let words := (line.splitOn " ").filter (!·.isEmpty)
    if words.contains "import" then
      words.getLast?.map fun module => (module.toName, index + 1, line.trimAscii.toString)
    else none

def challengeImports (file : System.FilePath) : IO (Array Name) := do
  return (← parseImports' (← IO.FS.readFile file) file.toString).imports.map (·.module)

def headerImports (file : System.FilePath) : IO (Array ImportFact) := do
  let header ← try some <$> parseImports' (← IO.FS.readFile file) file.toString catch _ => pure none
  return ((header.map (·.imports)).getD #[]).map fun found => { name := found.module, comptime := found.isMeta }


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

def describe (short : Name → String) (line : Headline) : String :=
  let assumed := line.assumptions.map fun assumption =>
    let label := if (line.assumptions.filter (·.claim == assumption.claim)).size > 1 then assumption.statement
      else short assumption.claim
    let unused := if assumption.unused then ", unused by the proof" else ""
    s!"{label} ({assumption.checks} {if assumption.checks == 1 then "check" else "checks"}{unused})"
  let stated := if assumed.isEmpty then short line.name
    else s!"{short line.name}  assumes {", ".intercalate assumed.toList}"
  let marks := (if line.proved then [] else [line.marker]) ++ line.killMark.toList ++ line.witnessMark.toList
  marks.foldl (fun shown mark => s!"{shown}  ({mark})") stated

structure Arguments where
  executable : Bool := false
  roots : Array Name := #[]
  target : Bool := false
  hidden : Array (String × String) := #[]
  challengeFile : String := ""
  challengeOLean : String := ""
  sources : Array (Name × String) := #[]

private def parse (args : List String) : Option Arguments := do
  let flags := args.takeWhile (·.startsWith "--")
  let challengeFile :: challengeOLean :: modules := args.dropWhile (·.startsWith "--") | none
  return {
    executable := flags.any (·.startsWith "--executable")
    roots := (flags.filterMap fun flag => (flag.dropPrefix? "--executable=").map (·.toString.toName)).toArray
    target := flags.contains "--target"
    hidden := (flags.filterMap fun flag => match flag.splitOn "=" with
      | ["--hidden", name, dir] => some (name, dir)
      | _ => none).toArray
    challengeFile, challengeOLean
    sources := modules.toArray.map fun module => match module.splitOn "=" with
      | [name, file] => (name.toName, file)
      | _ => (module.toName, module) }

private def gather (project : Project) (arguments : Arguments) (solution : Option Name) : IO Facts := do
  let challenge ← readChallenge project challengeModule arguments.challengeOLean
    (← IO.FS.readFile arguments.challengeFile)
  let catalog := arguments.sources.map (·.1)
  let imports ← arguments.sources.mapM fun (module, file) => return (module, ← importLines file)
  let texts ← arguments.sources.mapM fun (module, file) => do
    return (module, ← try IO.FS.readFile file catch _ => pure "")
  let facts ← withEnvironment catalog <| Meta.MetaM.run' do
    let env ← getEnv
    let moduleOf := fun (name : Name) =>
      (env.getModuleIdxFor? name).map (env.header.modules[·.toNat]!.module)
    let inventory ← collect catalog (NameSet.ofList (challenge.terminating.map (·.1)).toList)
    let blames ← blamesOf inventory
    let unsound := NameSet.ofList ((inventory.declarations.filter (!·.axioms.isEmpty)).map (·.name)).toList
    let packaged := NameSet.ofList catalog.toList
    let running := fun name => (moduleOf name).any packaged.contains
    let evidence := (allEvidence env).filter fun found => (moduleOf found.source).any packaged.contains
    let solutionImports := match solution with
      | some solution => importClosure env solution
      | none => NameSet.ofList env.header.moduleNames.toList
    let standings ← challenge.declared.mapM fun stated => do
      let auxiliaries := ((challenge.auxiliaries.find? (·.1 == stated.name)).map (·.2)).getD #[]
      let current ← standing env moduleOf solutionImports auxiliaries stated
      return (stated.name, match current with
        | .holds module => if unsound.contains stated.name then .unsound module else current
        | _ => current)
    let cyclic := match solution with
      | some solution => standings.filterMap fun (_, current) => match current with
        | .outside module => if (importClosure env module).contains solution then some module else none
        | _ => none
      | none => #[]
    let markOf := fun (kind : String) (names : Array Name) => names.findSome? fun name =>
      match (standings.find? (·.1 == name)).map (·.2) with
      | some (.holds _) => none
      | some current => some s!"{kind} {current.marker}"
      | none => some s!"{kind} not yet proved"
    let headlines ← challenge.headlines.mapM fun name => do
      let current := ((standings.find? (·.1 == name)).map (·.2)).getD .absent
      let prover := match current with
        | .holds module => some module
        | _ => none
      let analysed ← try headline project evidence name ((challenge.statement? name).getD (.sort .zero)) prover
        catch _ => pure { name, assumptions := #[], unnamed := #[] }
      return { analysed with
        proved := prover.isSome, marker := current.marker
        killMark := markOf "kill" (challenge.killsOf name), witnessMark := markOf "witness" (challenge.witnessesOf name) }
    let mut lines : Std.HashMap (Name × Name) Nat := {}
    let mut written : Std.HashMap Name String := {}
    let mut firstLines : Std.HashMap Name String := {}
    for (module, source) in texts do
      if let some index := env.getModuleIdx? module then
        for info in env.header.moduleData[index.toNat]!.constants do
          if let some ranges := rangesIn env index info.name then
            lines := lines.insert (module, info.name) ranges.range.pos.line
            if let some text := textAt source ranges.selectionRange then written := written.insert info.name text
            if let some text := lineAt source ranges.range.pos.line then
              firstLines := firstLines.insert info.name text
    let computationalHole := fun (hole : Name) =>
      inventory.declarations.any fun fact => fact.name == hole && fact.computational
    let lints := (Linter.getAllLints env).flatMap fun (module, entries) =>
      if packaged.contains module then entries.map (module, ·) else #[]
    let parents := declarationParents env inventory
    return {
      inventory, blames, challenge, headlines, standings, cyclic, lines, written, firstLines, lints, parents
      duplicates := duplicatesIn env catalog
      noncomputableHoles := challenge.holes.filter fun hole => isNoncomputable env hole && computationalHole hole
      fixpoints := challenge.holes.filter (fixpoint env ·)
      holes := challenge.holes.map fun hole => (hole, moduleOf hole)
      registrations := catalog.flatMap fun module =>
        (PersistentEnvExtension.getModuleEntries claimsExt env (env.getModuleIdx? module).get!).map
          fun claim => (claim, module, project.role? module, moduleOf claim)
      terminations := terminations (fixpoint env) challenge.terminating challenge.statement?
      entry := entryOf project env moduleOf running challenge.holes : Facts }
  return { facts with
    files := arguments.sources, imports, challengeFile := arguments.challengeFile, roots := arguments.roots
    solution := solution.getD .anonymous, hidden := arguments.hidden }

private def listing (title : String) (items : Array String) : String :=
  "\n".intercalate (s!"{title}: {items.size}" :: items.toList.map fun item => "  " ++ item.replace "\n" "\n    ")

private def lockText (current : Array (String × UInt64)) : String :=
  "\n".intercalate (current.map fun (file, digest) => s!"{digest} {file}").toList

private def statementAudit (arguments : Arguments) : IO UInt32 := do
  let catalog := arguments.sources.map (·.1)
  let project := Project.ofPackage catalog arguments.executable
  let challenge ← readChallenge project challengeModule arguments.challengeOLean
    (← IO.FS.readFile arguments.challengeFile)
  let solution := solutionOf catalog
  let specs := arguments.sources.filter (project.role? ·.1 matches some .coreSpec | some .worldSpec)
  let facts : Facts := {
    challenge, files := arguments.sources, challengeFile := arguments.challengeFile
    challengeImports := ← challengeImports arguments.challengeFile
    imports := #[(challengeModule, ← importLines arguments.challengeFile)] ++
      (← specs.mapM fun (module, file) => return (module, ← importLines file))
    specImports := ← specs.mapM fun (module, file) => return (module, ← headerImports file)
    terminations := terminations (fun _ => false) challenge.terminating challenge.statement? }
  let ownedNow ← ownedFiles project arguments.sources arguments.challengeFile
  let current ← digests ownedNow
  let locked ← readLock
  let lockFailures := (locked.map fun locked =>
    lockErrors locked current (editableFiles project arguments.sources) arguments.challengeFile "lake build").getD #[]
  let solutionErrors := match solution with | .ok _ => #[] | .error error => #[error]
  let specErrors ← if specs.isEmpty || !lockFailures.isEmpty then pure #[] else
    try pure (ownedViolations project (← gather project { arguments with sources := specs } none) false)
    catch failure => pure #[s!"the statement check cannot load the CoreSpec and WorldSpec modules together: \
      {failure}. Fix what Lean reports in those modules, {relockNext}."]
  let errors := if lockFailures.isEmpty then
      meaningful facts ++ owned project facts ++ specErrors ++ stated facts ++ solutionErrors
    else lockFailures ++ solutionErrors
  unless errors.isEmpty do
    IO.println (listing "Errors" errors)
    return 1
  if let .ok solution := solution then
    let config := comparatorConfig solution challenge
    unless (← try some <$> IO.FS.readFile "comparator.json" catch _ => pure none) == some config do
      IO.FS.writeFile "comparator.json" config
      IO.println s!"Wrote comparator.json: {challenge.theorems.size} theorems and {challenge.holes.size} \
        definitions for `lake comparator` to check against {solution}"
  if locked.isNone then
    IO.FS.writeFile "owned.lock" (lockText current)
    IO.println s!"Recorded owned.lock: {" ".intercalate ownedNow.toList}"
  return 0

private def holdsIn (facts : Facts) (name : Name) : Bool :=
  facts.standings.any fun (found, current) => found == name && current matches .holds _

private def proved (facts : Facts) : String :=
  let counted := fun (names : Array Name) (label : String) =>
    if names.isEmpty && label != "headlines" then none
    else some s!"{(names.filter (holdsIn facts)).size} of {names.size} {label}"
  "Proved: " ++ ", ".intercalate ([counted facts.challenge.headlines "headlines",
    counted (facts.challenge.kills.map (·.1)) "kills",
    counted (facts.challenge.witnesses.map (·.1)) "witnesses"].filterMap id)

private def solutionAudit (arguments : Arguments) : IO UInt32 := do
  let catalog := arguments.sources.map (·.1)
  let project := Project.ofPackage catalog arguments.executable
  let solution := solutionOf catalog
  let facts ← try gather project arguments solution.toOption catch failure => do
    IO.println (listing "Errors" #[s!"the audit cannot load the package's modules together: {failure}. When Lean \
      reports a name already declared, two modules of the package declare it, or two define `main`: rename one of \
      them, {lintNext}."])
    return 1
  let edit := editableFiles project arguments.sources
  let ownedNow ← ownedFiles project arguments.sources arguments.challengeFile
  let current ← digests ownedNow
  let existing ← try some <$> IO.FS.readFile "comparator.json" catch _ => pure none
  let lock ← readLock
  let lockFailures := match lock with
    | some locked => lockErrors locked current edit arguments.challengeFile
    | none => #[if arguments.target then s!"owned.lock is missing, so lint cannot check that the owned files are \
        unchanged. Restore it with `git checkout -- owned.lock`, or run `lake build` to record the current \
        statement, {lintNext}." else noTargetError]
  let drifted := lock.isSome && !lockFailures.isEmpty
  let comparator := match solution with
    | .ok solution => if drifted then #[] else
      comparatorErrors (comparatorConfig solution facts.challenge) existing arguments.target
    | .error error => #[error]
  let errors := distinct (ownedViolations project facts true ++ sound project facts ++ registered project facts ++
    evidenced facts ++ warned facts ++ lockFailures ++ comparator)
  let items := if drifted then #[] else pending facts
  let short := shorten (sharedNamespace (facts.headlines.map (·.name)))
  let mut report := facts.headlines.map (describe short) |>.push (proved facts)
  let independent := (facts.challenge.headlines.filter fun headline =>
    facts.challenge.independent.any fun (target, kill) => target == headline && holdsIn facts kill).size
  if independent > 0 then report := report.push s!"Independent: {independent} of {facts.headlines.size} headlines"
  for t in facts.terminations do report := report.push s!"{short t.definition} terminates via {short t.headline}"
  unless errors.isEmpty do report := report.push (listing "Errors" errors)
  unless items.isEmpty do report := report.push (listing "Pending" items)
  report := report.push s!"Edit: {" ".intercalate edit.toList}" |>.push s!"Owned: {" ".intercalate ownedNow.toList}"
  IO.println ("\n".intercalate report.toList)
  return if !errors.isEmpty || !project.check facts.inventory then 1 else if items.isEmpty then 0 else 2

def run (args : List String) : IO UInt32 := do
  let usage := "usage: lean --run Audit.lean (statement | solution) [--executable[=<root module>]]... [--target] \
    [--hidden=<package>=<dir>]... <challenge file> <challenge olean> <module>=<file>..."
  match args with
  | "statement" :: rest => if let some arguments := parse rest then statementAudit arguments else
    IO.eprintln usage
    return 1
  | "solution" :: rest => if let some arguments := parse rest then solutionAudit arguments else
    IO.eprintln usage
    return 1
  | _ => do
    IO.eprintln usage
    return 1

end SoftwareChallenge.Audit

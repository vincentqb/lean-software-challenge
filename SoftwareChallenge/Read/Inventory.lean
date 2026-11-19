module

public meta import Lean
public meta import SoftwareChallenge.Commands.Extensions
public meta import SoftwareChallenge.CoreCode.Facts
public meta import SoftwareChallenge.CoreCode.Graph
public meta import SoftwareChallenge.Read.Source
public meta import SoftwareChallenge.Read.Files
public meta import SoftwareChallenge.Read.Environment

public section
meta section

open Lean Meta

namespace SoftwareChallenge.Read

structure CatalogModule where
  name : Name
  index : ModuleIdx
  data : ModuleData
  file : String
  source : String
  written : Array ImportLine

def catalogModules (lake : LakeFacts) (catalog : Array Name) (imported : Imported) (next : Next) :
    IO (Array CatalogModule) :=
  catalog.mapM fun name => do
    let file := fileOf lake name
    let some (index, data) := imported.compiled? name
      | throw <| .userError s!"{file}:1: lake.json lists {name}, but its compiled module did not load, so the step \
          cannot read it. Run `lake build {name}`, then run `{next.command}`."
    let source ← if named lake file then readSource lake file next else pure ""
    return { name, index, data, file, source, written := ← importLines name file source }

def CatalogModule.imports (module : CatalogModule) : Array ImportLine :=
  placedImports module.name module.data module.written

def CatalogModule.place (module : CatalogModule) (env : Environment) (name : Name) : Place :=
  { file := module.file, line := ((rangesIn env module.index name).map (·.range.pos.line)).getD 0 }

def moduleFact (module : CatalogModule) : ModuleFact :=
  { name := module.name, file := module.file, usesModuleSystem := module.data.isModule
    imports := module.imports.map (·.fact) }

abbrev AxiomWalk := StateRefT (Std.HashMap Name (Array Name)) MetaM

def directUses (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] ++
    match info with | .inductInfo ind => ind.ctors.toArray | _ => #[]

def joined (found more : Array Name) : Array Name :=
  more.foldl (fun found name => if found.contains name then found else found.push name) found

mutual

partial def axiomsOf (name : Name) : AxiomWalk (Array Name) := do
  if let some known := (← get)[name]? then return known
  modify (·.insert name #[])
  let found ← if !isPrivateName name then collectAxioms name else
    match (← getEnv).find? name with
    | some info => ownAxioms info
    | none => pure #[]
  modify (·.insert name found)
  return found

partial def ownAxioms (info : ConstantInfo) : AxiomWalk (Array Name) := do
  let mut found := if info.isAxiom then #[info.name] else #[]
  for used in directUses info do
    unless used == info.name do found := joined found (← axiomsOf used)
  return found.qsort Name.lt

end

def culpritOf (bad : Name) (own : ConstantInfo) : AxiomWalk Name := do
  let env ← getEnv
  let mut frontier := #[own.name]
  let mut seen : NameSet := {}
  while !frontier.isEmpty do
    let mut next := #[]
    for name in frontier do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := (if name == own.name then some own else none).orElse fun _ => env.find? name | continue
      let uses := directUses info
      if uses.contains bad then return name
      for used in uses do
        if !seen.contains used && (← axiomsOf used).contains bad then next := next.push used
    frontier := next
  return own.name

def terminates (env : Environment) (name : Name) : Bool :=
  (Elab.Structural.eqnInfoExt.find? env name).isSome || (Elab.WF.eqnInfoExt.find? env name).isSome

def fixpoint (env : Environment) (name : Name) : Bool :=
  (Elab.PartialFixpoint.eqnInfoExt.find? env name).isSome

def derivedInstance (env : Environment) (name : Name) : Bool :=
  (Compiler.isUnsafeRecName? name).any fun source => Meta.isInstanceCore env source.getPrefix

def computational (info : ConstantInfo) : MetaM Bool := do
  unless info matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _ do return false
  if ← isProp info.type then return false
  forallTelescopeReducing info.type fun _ result => return !(← whnf result).isSort

def meaningDependencies (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | some (.inductInfo ind) => ind.ctors.toArray
  | some (.ctorInfo constructor) => constructor.type.getUsedConstants
  | some info => ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  | none => #[]

def meaningEdges (env : Environment) (roots : Array Name) : Array (Name × Array Name) := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut edges := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let next := meaningDependencies env name
    edges := edges.push (name, next)
    pending := pending ++ next
  return edges

def declarationFact (reachesIO : Std.HashSet Name) (terminating : Array Name) (module : CatalogModule)
    (info : ConstantInfo) : AxiomWalk DeclarationFact := do
  let env ← getEnv
  let ranges := rangesIn env module.index info.name
  let isComputational ← computational info
  return {
    name := info.name
    module := module.name
    line := (ranges.map (·.range.pos.line)).getD 0
    computational := isComputational
    isUnsafe := info.isUnsafe
    isPartial := info.isPartial && !(ranges.isNone && (derivedInstance env info.name ||
      (Compiler.isUnsafeRecName? info.name).any fun source =>
        terminates env source || terminating.contains source && fixpoint env source))
    external := isExtern env info.name
    unfoldable := info matches .defnInfo _
    replaced := (Compiler.getImplementedBy? env info.name).isSome
    initializes := (getInitFnNameFor? env info.name).isSome
    effects := isComputational && info.type.getUsedConstants.any reachesIO.contains
    debug := info.getUsedConstantsAsSet.any fun used => used.isAtomic && "dbg".isPrefixOf used.toString
    axioms := ← ownAxioms info }

def blameOf (env : Environment) (fact : DeclarationFact) (own : ConstantInfo) (axiomName : Name) :
    AxiomWalk AxiomBlame := do
  let culprit ← culpritOf axiomName own
  return { declaration := fact.name, axiomName, culprit, culpritModule? := moduleOf? env culprit }

def parentOf? (env : Environment) (name : Name) : Option Name :=
  match env.find? name with
  | some (.ctorInfo info) => some info.induct
  | some (.recInfo _) => some name.getPrefix
  | _ => match env.getProjectionFnInfo? name with
    | some projection => some projection.ctorName.getPrefix
    | none => if isAuxRecursor env name || isNoConfusion env name then some name.getPrefix else none

def parentsOf (env : Environment) (modules : Array CatalogModule) : Array (Name × Name) :=
  modules.flatMap fun module => module.data.constants.filterMap fun info =>
    (parentOf? env info.name).map (info.name, ·)

def registrationsOf (env : Environment) (modules : Array CatalogModule) : Array RegistrationFact :=
  modules.flatMap fun module =>
    (PersistentEnvExtension.getModuleEntries claimsExt env module.index).map fun claim =>
      let home? := moduleOf? env claim
      { claim, module := module.name, home?
        place := if home? == some module.name then module.place env claim else { file := module.file, line := 0 } }

def placesOf (env : Environment) (modules : Array CatalogModule) : Array DeclarationPlace :=
  modules.flatMap fun module => module.data.constants.filterMap fun info =>
    (rangesIn env module.index info.name).map fun ranges =>
      { name := info.name, place := { file := module.file, line := ranges.range.pos.line }
        written := textAt module.source ranges.selectionRange
        firstLine := lineAt module.source ranges.range.pos.line }

def derivedPartialsOf (env : Environment) (modules : Array CatalogModule) : Array (Name × Name) :=
  modules.flatMap fun module =>
    (module.data.constants.filter fun info => info.isPartial && derivedInstance env info.name).map
      (·.name, module.name)

structure InventoryFacts where
  inventory : Inventory
  blames : Array AxiomBlame
  meanings : Array (Name × Array Name)

def inventoryFacts (modules : Array CatalogModule) (terminating : Array Name) : MetaM InventoryFacts := do
  let env ← getEnv
  let types := modules.flatMap fun module => module.data.constants.flatMap (·.type.getUsedConstants)
  let meanings := meaningEdges env types
  let reachesIO := Graph.dependingOn (Graph.ofEdges meanings) #[``IO.RealWorld]
  StateRefT'.run' (s := {}) do
    let mut declarations := #[]
    let mut blames := #[]
    for module in modules do
      for info in module.data.constants do
        let fact ← declarationFact reachesIO terminating module info
        declarations := declarations.push fact
        for axiomName in fact.axioms do
          unless standardAxioms.contains axiomName do
            blames := blames.push (← blameOf env fact info axiomName)
    return { inventory := { modules := modules.map moduleFact, declarations }, blames, meanings }

end SoftwareChallenge.Read

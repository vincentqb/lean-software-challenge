module

public meta import Lean
public meta import SoftwareChallenge.Commands
public meta import SoftwareChallenge.CoreCode.Facts
public meta import SoftwareChallenge.Read.Source
public meta import SoftwareChallenge.Read.Files
public meta import SoftwareChallenge.Read.Constants
public meta import SoftwareChallenge.Read.Environment
public meta import SoftwareChallenge.Read.Inventory
public meta import SoftwareChallenge.CoreCode.Rules.Statement

public section
meta section

open Lean Meta

namespace SoftwareChallenge.Read

def isHole (info : ConstantInfo) : Bool :=
  match info with
  | .defnInfo value => value.value.hasSorry
  | .opaqueInfo value => value.value.hasSorry
  | _ => false

def foreignIn (env : Environment) : Array Name :=
  (env.header.moduleNames.zip env.header.moduleData).flatMap fun (module, data) =>
    if Role.ofName module == .worldSpec then data.constNames.filter (isExtern env ·) else #[]

def lastOf : Name → String
  | .str _ last => last
  | name => toString name

def killTemplate (type : Expr) (replaced : Array Name) : MetaM String := do
  let mut holes : Std.HashMap Name Expr := {}
  for name in replaced do
    if let some (.const _ levels) := type.find? (·.isConstOf name) then
      holes := holes.insert name (← mkFreshExprMVar (← inferType (.const name levels))
        (userName := Name.mkSimple s!"wrong_{lastOf name}"))
  let held := holes
  let wrong := type.replace fun expr => match expr with
    | .const name _ => held[name]?
    | _ => none
  shown (mkNot wrong)

def auxiliariesOf (env : Environment) (index : ModuleIdx) (targets : NameSet) (root : ConstantInfo) :
    Array ConstantInfo := Id.run do
  let auxiliary := fun (name : Name) => env.getModuleIdxFor? name == some index && !targets.contains name
  let mut pending := root.type.getUsedConstants.filter auxiliary
  let mut seen : NameSet := {}
  let mut found := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    found := found.push info
    pending := pending ++ (directUses info).filter auxiliary
  return found.qsort (toString ·.name < toString ·.name)
where
  directUses (info : ConstantInfo) : Array Name :=
    info.type.getUsedConstants ++ ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]

structure Placed where
  info : ConstantInfo
  ranges : DeclarationRanges

def Placed.before (earlier later : Placed) : Bool :=
  earlier.ranges.range.pos.line < later.ranges.range.pos.line ||
    earlier.ranges.range.pos.line == later.ranges.range.pos.line &&
      earlier.ranges.range.pos.column < later.ranges.range.pos.column

def binderFacts (locals : Array Expr) : MetaM (List BinderFact) := do
  let mut found := #[]
  for (binder, index) in locals.zipIdx do
    let earlier := locals.extract 0 index
    let type ← inferType binder
    let meaning ← Telescope.unfolded type
    let (conclusion, variables) ← forallTelescope meaning fun peeled body => do
      let chosen ← peeled.filterMapM fun bound => do
        if ← isProp (← inferType bound) then return none
        return some (toString (← bound.fvarId!.getUserName).eraseMacroScopes)
      return (← shown body, chosen)
    found := found.push {
      name := toString (← binder.fvarId!.getUserName).eraseMacroScopes
      type := Shape.ofExpr (type.abstract earlier)
      meaning := Shape.ofExpr (meaning.abstract earlier)
      prop := ← isProp type
      shown := ← shown type
      conclusion, variables
      level := Universe.ofLevel (← getLevel type).normalize }
  return found.toList

def headlineFact (replaceable : Name → Bool) (holes foreign : Array Name) (target : TargetFact)
    (info : ConstantInfo) : MetaM HeadlineFact := do
  let used := info.type.getUsedConstants
  let replaced := if used.any holes.contains then used.filter holes.contains else used.filter foreign.contains
  let killTemplate? ← if replaced.isEmpty then pure none else some <$> killTemplate info.type replaced
  let witness? ← (← Telescope.witnessType replaceable info.type).mapM shown
  let telescope ← forallTelescope (← Telescope.unfolded info.type) fun locals _ => binderFacts locals
  return { target, telescope, killTemplate?, witness? }

def emptyChallenge (module : Name) (file : String) : ChallengeFacts :=
  { module, file, runtimeImports := #[], metaImports := #[], closure := #[], headlines := #[], kills := #[],
    witnesses := #[], holes := #[], filled := #[], axioms := #[], terminating := #[], replaceable := #[] }

def ownedFacts (lake : LakeFacts) (challenge : Name) (imported : Imported) (next : Next) : IO OwnedFacts := do
  let env := imported.env
  let names := (lake.modules.map (·.module)).filter fun module =>
    module != challenge && (env.getModuleIdx? module).isSome
  let modules ← catalogModules lake names imported next
  runIn env do
    let read ← inventoryFacts modules #[]
    return {
      inventory := read.inventory
      imports := modules.flatMap (·.imports)
      blames := read.blames
      registrations := registrationsOf env modules
      places := placesOf env modules
      parents := parentsOf env modules }

def challengeFacts (lake : LakeFacts) (challenge : SourceFact) (imported : Imported) (next : Next) :
    IO ChallengeFacts := do
  let env := imported.env
  let some (index, data) := moduleData? env challenge.module
    | throw <| .userError s!"{challenge.file}:1: {challenge.module} did not load from its compiled module, so its \
        statements cannot be read. Run `lake build {challenge.module}`, then run `{next.command}`."
  let source ← readSource lake challenge.file next
  let imports := placedImports challenge.module data (← importLines challenge.module challenge.file source)
  let rangesOf := fun (name : Name) => rangesIn env index name
  let placeOf := fun (name : Name) =>
    let line := ((rangesOf name).orElse fun _ => rangesOf (ownerOf name)).map (·.range.pos.line)
    ({ file := challenge.file, line := line.getD 0 } : Place)
  let written := (data.constants.filterMap fun info =>
    if (privateToUserName info.name).isInternal then none
    else (rangesOf info.name).map fun ranges => ({ info, ranges } : Placed)).qsort Placed.before
  let theorems := written.filter (·.info.isTheorem)
  let holes := written.filter fun placed => !placed.info.isTheorem && isHole placed.info
  let targetNames := NameSet.ofList ((theorems ++ holes).map (·.info.name)).toList
  let killLinks := moduleLinks env index .kills
  let witnessLinks := moduleLinks env index .witness
  let foreign := foreignIn env
  let replaceable := holes.map (·.info.name) ++ foreign
  let auxiliaries := fun (placed : Placed) => auxiliariesOf env index targetNames placed.info
  let auxiliaryNames := NameSet.ofList
    ((theorems ++ holes).flatMap fun placed => (auxiliaries placed).map (·.name)).toList
  let isWritten := fun (name : Name) => written.any (·.info.name == name)
  let accounted := fun (info : ConstantInfo) =>
    targetNames.contains info.name || info.isAxiom || !isWritten info.name && auxiliaryNames.contains info.name
  let writtenOf := fun (placed : Placed) => textAt source placed.ranges.selectionRange
  runIn env do
    let targetOf := fun (placed : Placed) (writtenName : String) (derived : Bool) => do
      let (rendered, renderedExplicit) ← render placed.info.type
      return ({
        constant := constantFact placed.info
        place := { file := challenge.file, line := placed.ranges.range.pos.line }
        written := writtenName
        enclosingNamespace := namespaceOf (privateToUserName placed.info.name) writtenName
        signature := if derived then "" else signatureAt source placed.ranges.selectionRange.endPos
        rendered, renderedExplicit
        auxiliaries := (auxiliaries placed).map constantFact } : TargetFact)
    let isKill := fun (name : Name) => killLinks.any (·.1 == name)
    let derivedOf := fun (name : Name) => witnessLinks.find? (·.1 == name)
    let mut statedWitnesses := #[]
    for placed in theorems do
      if isKill placed.info.name || (derivedOf placed.info.name).isSome then continue
      let some headline := theorems.find? (witnessName ·.info.name == placed.info.name) | continue
      if killLinks.any (·.2 == headline.info.name) then
        statedWitnesses := statedWitnesses.push (placed.info.name, headline)
    let mut headlines := #[]
    let mut kills := #[]
    let mut witnesses := #[]
    for placed in written do
      for (_, headline) in killLinks.filter (·.1 == placed.info.name) do
        kills := kills.push { target := ← targetOf placed (writtenOf placed) false, headline : KillFact }
    for placed in theorems do
      let name := placed.info.name
      if let some (_, headline) := derivedOf name then
        let headlineWritten := ((theorems.find? (·.info.name == headline)).map writtenOf).getD (lastOf headline)
        witnesses := witnesses.push
          { target := ← targetOf placed (headlineWritten ++ "_applies") true, headline, derived := true : WitnessFact }
      else if let some (_, headline) := statedWitnesses.find? (·.1 == name) then
        witnesses := witnesses.push
          { target := ← targetOf placed (writtenOf placed) false, headline := headline.info.name, derived := false }
      else unless isKill name do
        let target ← targetOf placed (writtenOf placed) false
        let read ← try headlineFact replaceable.contains (holes.map (·.info.name)) foreign target placed.info
          catch failure => throwError "{target.place.file}:{target.place.line}: the step could not read headline \
            {name} ({failure.toMessageData}), so it cannot tell which claims, preconditions and witness it states; \
            no edit to the package fixes this. Fix SoftwareChallenge/Read so that it reads the headline, then run \
            `{next.command}`."
        headlines := headlines.push read
    let holeTargets ← holes.mapM fun placed => targetOf placed (writtenOf placed) false
    return {
      module := challenge.module
      file := challenge.file
      runtimeImports := imports.filter (!·.fact.comptime)
      metaImports := imports.filter (·.fact.comptime)
      closure := env.header.moduleNames.filter (· != challenge.module)
      headlines, kills, witnesses
      holes := holeTargets
      filled := (data.constants.filter (!accounted ·)).map fun info => (info.name, placeOf info.name)
      axioms := (data.constants.filter (·.isAxiom)).map fun info => (info.name, placeOf info.name)
      terminating := (moduleLinks env index .terminates).map fun (headline, definition) =>
        { definition, headline, place := placeOf headline }
      replaceable
      imports := (env.header.moduleNames.zip env.header.moduleData).map fun (module, data) =>
        (module, data.imports.map (·.module))
      claims := claimsExt.getState env }

end SoftwareChallenge.Read

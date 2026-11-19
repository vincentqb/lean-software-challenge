module

public meta import Lean
public meta import SoftwareChallenge.Commands
public meta import SoftwareChallenge.CoreCode.Facts
public meta import SoftwareChallenge.Read.Source
public meta import SoftwareChallenge.Read.Files
public meta import SoftwareChallenge.Read.Constants
public meta import SoftwareChallenge.Read.Environment
public meta import SoftwareChallenge.Read.Inventory
public meta import SoftwareChallenge.Read.Checks

public section
meta section

open Lean Meta

namespace SoftwareChallenge.Read

def namedSolution : Name → Bool
  | .str _ last => last == "Solution"
  | _ => false

def importClosure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut found := #[]
  while !pending.isEmpty do
    let module := pending.back!
    pending := pending.pop
    if seen.contains module then continue
    seen := seen.insert module
    found := found.push module
    if let some (_, data) := moduleData? env module then pending := pending ++ data.imports.map (·.module)
  return found

def usedBinders (type value : Expr) : MetaM (Array Nat) := do
  forallTelescope (← Telescope.unfolded type) fun locals _ => do
    let mut used := #[]
    let mut body := value
    for (binder, index) in locals.zipIdx do
      match body.consumeMData with
      | .lam _ _ inner _ =>
        if inner.hasLooseBVar 0 then used := used.push index
        body := inner.instantiate1 binder
      | _ => return used ++ (List.range (locals.size - index)).toArray.map (· + index)
    return used

def compiledCallees (env : Environment) (info : ConstantInfo) : Array Name :=
  let compiled := (env.find? (Compiler.mkUnsafeRecName info.name)).getD info
  ((compiled.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]

def usesSorry (info : ConstantInfo) : Bool :=
  info.type.hasSorry || (info.value? (allowOpaque := true)).any (·.hasSorry)

def serverReadable (lake : LakeFacts) (module : CatalogModule) : IO Bool := do
  unless module.data.isModule do return true
  let olean ← match ← artifactsOf lake module.name with
    | some arts => pure arts.olean?
    | none => some <$> findOLean module.name
  match olean with
  | some olean => (olean.addExtension "server").pathExists
  | none => return false

def lintsOf (env : Environment) (module : CatalogModule) : Array LintFact :=
  (Linter.lintLogExt.getModuleEntries env module.index (level := .server)).map fun entry =>
    { module := module.name, place := { file := module.file, line := (entry.position?.getD entry.message.pos).line }
      linter := entry.linter, message := entry.message.data }

def foundFact (env : Environment) (modules : Array CatalogModule) (name : Name) : MetaM (Option FoundFact) := do
  let some info := env.find? name | return none
  let module := (moduleOf? env name).getD .anonymous
  let place := match modules.find? (·.name == module) with
    | some found => found.place env name
    | none => { file := sourcePath module, line := 0 }
  let (rendered, renderedExplicit) ← render info.type
  return some { constant := constantFact info, module, place, compiled := !isNoncomputable env name, rendered,
                renderedExplicit }

def solutionFacts (lake : LakeFacts) (challenge : ChallengeFacts) (imported : Imported) (next : Next) :
    IO SolutionFacts := do
  let env := imported.env
  let modules ← catalogModules lake (catalog lake challenge.module) imported next
  let linted ← modules.filterM (serverReadable lake)
  let names := modules.map (·.name)
  let solution? := match names.filter namedSolution with
    | #[solution] => some solution
    | _ => none
  runIn env do
    let read ← inventoryFacts modules (challenge.terminating.map (·.definition))
    let owned := modules.flatMap fun module => module.data.constants.map (module, ·)
    let sought := distinct (challenge.targets.flatMap fun target =>
      #[target.constant.name] ++ target.auxiliaries.map (·.name))
    let found ← sought.filterMapM (foundFact env modules)
    let premiseUses ← found.filterMapM fun fact => do
      let some (.thmInfo info) := env.find? fact.constant.name | return none
      return some (fact.constant.name, ← usedBinders info.type info.value)
    let evidence ← catalogEvidence modules
    let closure := (solution?.map (importClosure env)).getD #[]
    return {
      solution?
      inventory := read.inventory
      blames := read.blames
      imports := modules.flatMap (·.imports)
      calls := owned.map fun (_, info) => (info.name, compiledCallees env info)
      proofUses := owned.filterMap fun (_, info) =>
        (info.value? (allowOpaque := true)).map fun value => (info.name, value.getUsedConstants)
      meanings := read.meanings
      found
      solutionClosure := closure
      importsSolution := match solution? with
        | some solution => names.filter fun module => module != solution && (importClosure env module).contains solution
        | none => #[]
      premiseUses
      claimUses := ← claimUses challenge evidence
      checks := evidence.map (·.2)
      registrations := modules.flatMap fun module =>
        (PersistentEnvExtension.getModuleEntries claimsExt env module.index).map fun claim =>
          let home? := moduleOf? env claim
          { claim, module := module.name, home?
            place := if home? == some module.name then module.place env claim else { file := module.file, line := 0 } }
      lints := modules.flatMap (lintsOf env)
      linted := linted.map (·.name)
      sorries := owned.filterMap fun (module, info) =>
        if usesSorry info then some (module.place env (if (rangesIn env module.index info.name).isSome then info.name
          else ownerOf info.name)) else none
      fixpoints := (owned.filter fun (_, info) => fixpoint env info.name).map (·.2.name)
      main? := (owned.find? fun (_, info) => info.name == `main).map fun (module, info) =>
        (module.name, module.place env info.name)
      places := owned.filterMap fun (module, info) => (rangesIn env module.index info.name).map fun ranges =>
        { name := info.name, place := { file := module.file, line := ranges.range.pos.line }
          written := textAt module.source ranges.selectionRange
          firstLine := lineAt module.source ranges.range.pos.line } }

end SoftwareChallenge.Read

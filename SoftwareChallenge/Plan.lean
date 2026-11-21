import Lean
import SoftwareChallenge.Attributes

namespace SoftwareChallenge

open Lean Meta

structure Source where
  module : Name
  file : String
  deriving FromJson

structure Plan where
  packageDir : String
  challenge : Source
  solution : Name
  modules : Array Source
  programs : Array Name
  tests : Option Name
  deriving FromJson

def Plan.load (file : System.FilePath) : IO Plan := do
  match Json.parse (← IO.FS.readFile file) >>= fromJson? with
  | .ok plan => return plan
  | .error problem => throw (.userError s!"{file}: {problem}")

def Plan.owns (plan : Plan) (module : Name) : Bool := plan.modules.any (·.module == module)

def Plan.fileOf (plan : Plan) (module : Name) : String :=
  ((plan.modules.find? (·.module == module)).map (·.file)).getD (sourceOf module)

def importEnv (module : Name) : IO Environment := do
  unsafe enableInitializersExecution
  let (root, _) ← readModuleData (← findOLean module)
  withImporting do
    let (_, imported) ← (importModulesCore #[{ module }] (isExported := true)).run
    finalizeImport imported #[{ module }] {} (leakEnv := false) (loadExts := true) (isModule := root.isModule)

def inEnv {α : Type} (env : Environment) (action : MetaM α) : IO α := do
  let (value, _) ← (action.run' {} {}).toIO { fileName := "", fileMap := default, maxHeartbeats := 0 } { env }
  return value

def moduleOf (env : Environment) (name : Name) : Name :=
  ((env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!)).getD env.mainModule

def Plan.inPackage (plan : Plan) (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).any (plan.owns env.header.moduleNames[·.toNat]!)

def lineOf (name : Name) : CoreM Nat := do
  return ((← findDeclarationRanges? name).map (·.range.pos.line)).getD 0

def Plan.place (plan : Plan) (name : Name) : CoreM String := do
  return s!"{plan.fileOf (moduleOf (← getEnv) name)}:{← lineOf name}"

def isWritten (name : Name) : CoreM Bool := do
  let some ranges ← findDeclarationRanges? name | return false
  return ranges.range != ranges.selectionRange

def shown (expr : Expr) : MetaM String := do
  return toString (← withOptions (fun options => (options.setBool `pp.funBinderTypes true).set `format.width (10000 : Nat))
    (ppExpr expr))

end SoftwareChallenge

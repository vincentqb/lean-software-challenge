module

public meta import Lean

public section
meta section

open Lean

namespace SoftwareChallenge

structure Evidence where
  claim : Name
  statement : Expr
  source : Name
  line : Nat

inductive LinkKind where
  | kills | terminates | witness
  deriving BEq

structure Link where
  kind : LinkKind
  source : Name
  target : Name

initialize claimsExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

initialize evidenceExt : SimplePersistentEnvExtension Evidence (Array Evidence) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

initialize linksExt : SimplePersistentEnvExtension Link (Array Link) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

def isWorldClaim (env : Environment) (name : Name) : Bool := (claimsExt.getState env).contains name

def conclusionHead : Expr → Name
  | .forallE _ _ body _ => conclusionHead body
  | .mdata _ expr => conclusionHead expr
  | conclusion => conclusion.getAppFn.constName

def moduleLinks (env : Environment) (module : ModuleIdx) (kind : LinkKind) : Array (Name × Name) :=
  ((PersistentEnvExtension.getModuleEntries linksExt env module).filter (·.kind == kind)).map
    fun link => (link.source, link.target)

def localLinks (env : Environment) (kind : LinkKind) : Array (Name × Name) :=
  ((linksExt.getEntries env).toArray.filter (·.kind == kind)).map fun link => (link.source, link.target)

end SoftwareChallenge

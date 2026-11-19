module

@[expose] public section

namespace SoftwareChallenge

open Lean

def Name.PlainCharacter (char : Char) : Prop :=
  char ≠ '.' ∧ char ≠ '"' ∧ char ≠ '\\' ∧ char ≠ '«' ∧ char ≠ '»' ∧ ' ' ≤ char

def Name.PlainComponent (component : String) : Prop :=
  match component.toList with
  | [] => False
  | first :: rest => first.isDigit = false ∧ ∀ char ∈ first :: rest, Name.PlainCharacter char

def Name.Plain : Name → Prop
  | .anonymous => False
  | .str parent component => (parent = .anonymous ∨ Name.Plain parent) ∧ Name.PlainComponent component
  | .num _ _ => False

structure Config where
  challenge : Name
  solution : Name
  theorems : Array Name
  definitions : Array Name
  axioms : Array Name
  deriving DecidableEq, Repr, Inhabited

def Config.Plain (config : Config) : Prop :=
  Name.Plain config.challenge ∧ Name.Plain config.solution ∧ (∀ name ∈ config.theorems, Name.Plain name) ∧
    (∀ name ∈ config.definitions, Name.Plain name) ∧ ∀ name ∈ config.axioms, Name.Plain name

namespace Lock

structure Entry where
  path : String
  digest : String
  deriving DecidableEq, Repr, Inhabited

inductive Violation where
  | unrecorded (path : String)
  | differs (path : String)
  | missing (path : String)
  deriving DecidableEq, Repr, Inhabited

def digestOf (entries : Array Entry) (path : String) : Option String :=
  (entries.find? (·.path == path)).map (·.digest)

end Lock

end SoftwareChallenge

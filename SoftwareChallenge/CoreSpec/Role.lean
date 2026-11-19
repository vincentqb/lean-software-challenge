module

public import Lean.Data.Name

@[expose] public section

namespace SoftwareChallenge

open Lean

inductive Role where
  | coreSpec | worldSpec | coreCode | worldCode | tooling
  deriving DecidableEq, Repr, Inhabited

instance : ToString Role where
  toString
    | .coreSpec => "CoreSpec"
    | .worldSpec => "WorldSpec"
    | .coreCode => "CoreCode"
    | .worldCode => "WorldCode"
    | .tooling => "tooling"

def Role.Inner (role : Role) : Prop :=
  role = .coreSpec ∨ role = .worldSpec ∨ role = .coreCode

def Role.Owned (role : Role) : Prop :=
  role = .coreSpec ∨ role = .worldSpec

def Role.MayImport : Role → Role → Prop
  | .coreSpec, target => target = .coreSpec
  | .worldSpec, target => target = .coreSpec ∨ target = .worldSpec
  | .coreCode, target => target = .coreSpec ∨ target = .coreCode
  | .worldCode, target => target ≠ .tooling
  | .tooling, _ => True

def Role.ofName (name : Name) : Role :=
  (name.components.findSome? fun component =>
    [Role.coreSpec, .worldSpec, .coreCode, .worldCode].find? (toString · == component.toString)).getD .tooling

end SoftwareChallenge

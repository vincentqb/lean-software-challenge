module

@[expose] public section

namespace SoftwareChallenge

open Lean

inductive Universe where
  | zero
  | succ (level : Universe)
  | max (left right : Universe)
  | imax (left right : Universe)
  | param (name : Name)
  | mvar (name : Name)
  deriving DecidableEq, Repr, Inhabited

inductive Shape where
  | bvar (index : Nat)
  | fvar (name : Name)
  | mvar (name : Name)
  | sort (level : Universe)
  | const (name : Name) (levels : List Universe)
  | app (function argument : Shape)
  | lam (type body : Shape)
  | forallE (type body : Shape)
  | letE (type value body : Shape)
  | natLit (value : Nat)
  | strLit (value : String)
  | proj (structureName : Name) (index : Nat) (value : Shape)
  deriving DecidableEq, Repr, Inhabited

abbrev Witnesses := List (Name × Shape)

def Witnesses.find? : Witnesses → Name → Option Shape
  | [], _ => none
  | (key, witness) :: rest, name => if key = name then some witness else find? rest name

namespace Shape

def closedUnder (depth : Nat) : Shape → Bool
  | .bvar index => index < depth
  | .app function argument => function.closedUnder depth && argument.closedUnder depth
  | .lam type body | .forallE type body => type.closedUnder depth && body.closedUnder (depth + 1)
  | .letE type value body =>
    type.closedUnder depth && value.closedUnder depth && body.closedUnder (depth + 1)
  | .proj _ _ value => value.closedUnder depth
  | _ => true

def subst (replaceable : Name → Bool) (σ : Witnesses) : Shape → Shape
  | .const name levels => if replaceable name then (σ.find? name).getD (.const name levels) else .const name levels
  | .app function argument => .app (function.subst replaceable σ) (argument.subst replaceable σ)
  | .lam type body => .lam (type.subst replaceable σ) (body.subst replaceable σ)
  | .forallE type body => .forallE (type.subst replaceable σ) (body.subst replaceable σ)
  | .letE type value body =>
    .letE (type.subst replaceable σ) (value.subst replaceable σ) (body.subst replaceable σ)
  | .proj structureName index value => .proj structureName index (value.subst replaceable σ)
  | term => term

def negation (statement : Shape) : Shape := .app (.const ``Not []) statement

def conjunction : List Shape → Shape
  | [] => .const ``True []
  | [statement] => statement
  | statement :: rest => .app (.app (.const ``And []) statement) (conjunction rest)

end Shape

end SoftwareChallenge

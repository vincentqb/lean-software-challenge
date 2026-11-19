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

inductive Mentions (name : Name) : Shape → Prop where
  | const (levels : List Universe) : Mentions name (.const name levels)
  | appFunction {function argument : Shape} : Mentions name function → Mentions name (.app function argument)
  | appArgument {function argument : Shape} : Mentions name argument → Mentions name (.app function argument)
  | lamType {type body : Shape} : Mentions name type → Mentions name (.lam type body)
  | lamBody {type body : Shape} : Mentions name body → Mentions name (.lam type body)
  | forallEType {type body : Shape} : Mentions name type → Mentions name (.forallE type body)
  | forallEBody {type body : Shape} : Mentions name body → Mentions name (.forallE type body)
  | letEType {type value body : Shape} : Mentions name type → Mentions name (.letE type value body)
  | letEValue {type value body : Shape} : Mentions name value → Mentions name (.letE type value body)
  | letEBody {type value body : Shape} : Mentions name body → Mentions name (.letE type value body)
  | proj {structureName : Name} {index : Nat} {value : Shape} :
      Mentions name value → Mentions name (.proj structureName index value)

inductive Refers : Nat → Shape → Prop where
  | bvar (index : Nat) : Refers index (.bvar index)
  | appFunction {index : Nat} {function argument : Shape} :
      Refers index function → Refers index (.app function argument)
  | appArgument {index : Nat} {function argument : Shape} :
      Refers index argument → Refers index (.app function argument)
  | lamType {index : Nat} {type body : Shape} : Refers index type → Refers index (.lam type body)
  | lamBody {index : Nat} {type body : Shape} : Refers (index + 1) body → Refers index (.lam type body)
  | forallEType {index : Nat} {type body : Shape} : Refers index type → Refers index (.forallE type body)
  | forallEBody {index : Nat} {type body : Shape} : Refers (index + 1) body → Refers index (.forallE type body)
  | letEType {index : Nat} {type value body : Shape} : Refers index type → Refers index (.letE type value body)
  | letEValue {index : Nat} {type value body : Shape} : Refers index value → Refers index (.letE type value body)
  | letEBody {index : Nat} {type value body : Shape} : Refers (index + 1) body → Refers index (.letE type value body)
  | proj {index : Nat} {structureName : Name} {field : Nat} {value : Shape} :
      Refers index value → Refers index (.proj structureName field value)

def conclusion : Shape → Shape
  | .forallE _ body => body.conclusion
  | shape => shape

def appHead : Shape → Shape
  | .app applied _ => applied.appHead
  | shape => shape

def Concludes (shape : Shape) (claim : Name) : Prop :=
  ∃ levels, shape.conclusion.appHead = .const claim levels

def KilledBy (headline : Shape) (replaceable : Name → Bool) (others : List Shape) (kill : Shape) : Prop :=
  ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ headline.subst replaceable σ ≠ headline ∧
    (kill = (headline.subst replaceable σ).negation ∨
      others ≠ [] ∧ kill = conjunction ((headline.subst replaceable σ).negation :: others.map (·.subst replaceable σ)))

end Shape

end SoftwareChallenge

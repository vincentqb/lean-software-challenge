module

public import SoftwareChallenge.CoreSpec.Facts

@[expose] public section

namespace SoftwareChallenge

open Lean

def ChallengeFacts.isReplaceable (challenge : ChallengeFacts) (name : Name) : Bool :=
  challenge.replaceable.contains name

def Shape.constants : Shape → List Name
  | .const name _ => [name]
  | .app function argument => function.constants ++ argument.constants
  | .lam type body | .forallE type body => type.constants ++ body.constants
  | .letE type value body => type.constants ++ value.constants ++ body.constants
  | .proj _ _ value => value.constants
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .natLit _ | .strLit _ => []

def Shape.refers (index : Nat) : Shape → Bool
  | .bvar found => found == index
  | .app function argument => function.refers index || argument.refers index
  | .lam type body | .forallE type body => type.refers index || body.refers (index + 1)
  | .letE type value body => type.refers index || value.refers index || body.refers (index + 1)
  | .proj _ _ value => value.refers index
  | .fvar _ | .mvar _ | .sort _ | .const _ _ | .natLit _ | .strLit _ => false

def Shape.concludes? (shape : Shape) : Option Name :=
  match shape.conclusion.appHead with
  | .const name _ => some name
  | _ => none

def ChallengeFacts.isClaim (challenge : ChallengeFacts) : Name → Bool :=
  challenge.claims.contains

namespace Telescope

def depended (telescope : List BinderFact) (index : Nat) : Bool :=
  (List.range telescope.length).any fun later =>
    decide (index < later) && ((telescope[later]?).map fun binder => binder.type.refers (later - 1 - index)).getD false

def kindAt (claims : Name → Bool) (telescope : List BinderFact) (index : Nat) (binder : BinderFact) : BinderKind :=
  if depended telescope index || !binder.prop then .input
  else if binder.meaning.concludes?.any claims then .claim
  else .precondition

def refersAt (index : Nat) (binder : BinderFact) : List Nat :=
  (List.range index).filter fun earlier => binder.type.refers (index - 1 - earlier)

def binderAt (claims replaceable : Name → Bool) (telescope : List BinderFact) (index : Nat) (binder : BinderFact) :
    Binder :=
  { kind := kindAt claims telescope index binder, prop := binder.prop
    mentions := binder.meaning.constants.any replaceable, refers := refersAt index binder }

def summary (claims replaceable : Name → Bool) (telescope : List BinderFact) : List Binder :=
  telescope.zipIdx.map fun (binder, index) => binderAt claims replaceable telescope index binder

end Telescope

def HeadlineFact.binders (challenge : ChallengeFacts) (headline : HeadlineFact) : List Binder :=
  Telescope.summary challenge.isClaim challenge.isReplaceable headline.telescope

def Shape.remapFrom (remap : Nat → Nat) (depth : Nat) : Shape → Shape
  | .bvar index => if index < depth then .bvar index else .bvar (remap (index - depth) + depth)
  | .app function argument => .app (remapFrom remap depth function) (remapFrom remap depth argument)
  | .lam type body => .lam (remapFrom remap depth type) (remapFrom remap (depth + 1) body)
  | .forallE type body => .forallE (remapFrom remap depth type) (remapFrom remap (depth + 1) body)
  | .letE type value body =>
    .letE (remapFrom remap depth type) (remapFrom remap depth value) (remapFrom remap (depth + 1) body)
  | .proj structureName index value => .proj structureName index (remapFrom remap depth value)
  | other => other

namespace Witness

def conjunction : List Shape → Shape
  | [] => .const ``True []
  | [only] => only
  | first :: rest => .app (.app (.const ``And []) first) (conjunction rest)

def typeAt (telescope : List BinderFact) (index : Nat) : Shape :=
  ((telescope[index]?).map (·.type)).getD (.sort .zero)

def levelAt (telescope : List BinderFact) (index : Nat) : Universe :=
  ((telescope[index]?).map (·.level)).getD .zero

def placed (telescope : List BinderFact) (inputs : List Nat) (bound extra index : Nat) : Shape :=
  (typeAt telescope index).remapFrom (fun loose =>
    match inputs.findIdx? (· == index - 1 - loose) with
    | some position => extra + (bound - 1 - position)
    | none => loose) 0

def build (telescope : List BinderFact) (summary : List Binder) : Shape :=
  let kept := Telescope.kept summary
  let kindIs := fun (kind : BinderKind) (index : Nat) => (summary[index]?).any (·.kind == kind)
  let closed := fun (index : Nat) => (summary[index]?).any (·.refers.isEmpty)
  let inputs := kept.filter (kindIs .input)
  let claims := kept.filter (kindIs .claim)
  let inner := claims.filter fun index => !closed index
  let outer := claims.filter closed
  let preconditions := kept.filter (kindIs .precondition)
  let body := conjunction (preconditions.map (placed telescope inputs inputs.length inner.length))
  let premised := inner.zipIdx.foldr (fun (index, position) statement =>
    .forallE (placed telescope inputs inputs.length position index) statement) body
  let quantified := inputs.zipIdx.foldr (fun (index, position) statement =>
    let type := placed telescope inputs position 0 index
    .app (.app (.const ``Exists [levelAt telescope index]) type) (.lam type statement)) premised
  outer.foldr (fun index statement => .forallE (typeAt telescope index) statement) quantified

end Witness

def HeadlineFact.expectedWitness (challenge : ChallengeFacts) (headline : HeadlineFact) : Shape :=
  Witness.build headline.telescope (headline.binders challenge)

end SoftwareChallenge

module

@[expose] public section

namespace SoftwareChallenge

inductive BinderKind where
  | input | claim | precondition
  deriving DecidableEq, Repr, Inhabited

structure Binder where
  kind : BinderKind
  mentions : Bool
  refers : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace Telescope

inductive Needed (binders : List Binder) : Nat → Prop where
  | referredInput {index : Nat} {input referrer : Binder} :
      binders[index]? = some input → input.kind = .input → referrer ∈ binders →
      referrer.kind = .precondition → index ∈ referrer.refers → Needed binders index
  | mentioningInput {index : Nat} {input : Binder} :
      binders[index]? = some input → input.kind = .input → input.mentions = true → Needed binders index
  | referredPrecondition {index : Nat} {precondition referrer : Binder} :
      binders[index]? = some precondition → precondition.kind = .precondition → referrer ∈ binders →
      referrer.kind = .precondition → index ∈ referrer.refers → Needed binders index
  | referredByNeeded {index needed : Nat} {binder : Binder} :
      Needed binders needed → binders[needed]? = some binder → index ∈ binder.refers →
      index < binders.length → Needed binders index

def seeded (binders : List Binder) (index : Nat) : Bool :=
  let referred := binders.any fun referrer => referrer.kind == .precondition && referrer.refers.contains index
  match binders[index]? with
  | some binder => match binder.kind with
    | .input => binder.mentions || referred
    | .precondition => referred
    | .claim => false
  | none => false

def expand (binders : List Binder) (needed : List Nat) : List Nat :=
  (List.range binders.length).filter fun index =>
    needed.contains index || needed.any fun other => ((binders[other]?).map (·.refers.contains index)).getD false

def close (binders : List Binder) : Nat → List Nat → List Nat
  | 0, needed => needed
  | rounds + 1, needed => close binders rounds (expand binders needed)

def kept (binders : List Binder) : List Nat :=
  close binders binders.length ((List.range binders.length).filter (seeded binders))

def needsWitness (binders : List Binder) : Bool :=
  binders.any fun binder => binder.mentions && binder.kind != .claim

end Telescope

end SoftwareChallenge

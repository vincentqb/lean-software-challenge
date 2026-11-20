module

@[expose] public section

namespace SoftwareChallenge

inductive BinderKind where
  | input | claim | precondition
  deriving DecidableEq, Repr, Inhabited

structure Binder where
  kind : BinderKind
  prop : Bool
  mentions : Bool
  refers : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace Telescope

def heldMentioning (binders : List Binder) (earlier : Nat) : Bool :=
  match binders[earlier]? with
  | some held => held.prop && held.mentions
  | none => false

def seeded (binders : List Binder) (index : Nat) : Bool :=
  match binders[index]? with
  | some binder =>
    binder.prop || binder.kind == .input && (binder.mentions || binder.refers.any (heldMentioning binders))
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

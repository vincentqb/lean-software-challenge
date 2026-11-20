module

meta import Lean

public section

namespace SoftwareChallengeReadTests.Fixtures.CoreSpec.Forged

inductive Side where
  | left
  | right (n : Nat)

inductive Void : Type

set_option genCtorIdx false in
inductive Coin where
  | heads
  | tails

unsafe def Coin.ctorIdx._impl (coin : Coin) : Nat := getObjTagNat coin

@[implemented_by Coin.ctorIdx._impl] def Coin.ctorIdx (coin : Coin) : Nat :=
  Coin.casesOn (motive := fun _ => Nat) coin (nat_lit 0) (nat_lit 1)

set_option genCtorIdx false in
structure Box where
  value : Nat

set_option genCtorIdx false in
inductive Die where
  | one
  | two

set_option genCtorIdx false in
inductive Lot where
  | one
  | two

open Lean in
run_cmd Elab.Command.liftCoreM do
  let raw := `SoftwareChallengeReadTests.Fixtures.CoreSpec.Forged.Raw
  let ctors : List Constructor :=
    [{ name := raw ++ `a, type := mkConst raw }, { name := raw ++ `b, type := mkConst raw }]
  addDecl <| .inductDecl [] 0 [{ name := raw, type := mkSort .one, ctors }] false
  compileDecls #[raw]

def Raw.casesOn.{u} (_ : Raw → Sort u) (_ : Raw) (_ second : Nat) : Nat := second

open Lean in
run_cmd Elab.Command.liftCoreM do
  let nat := mkConst ``Nat
  for (ctorIdx, datatype, alternatives, readsTag) in [
      (``Box ++ `ctorIdx, ``Box, [.lam `value nat (mkRawNatLit 0) .default], true),
      (``Die ++ `ctorIdx, ``Die, [mkRawNatLit 1, mkRawNatLit 0], true),
      (``Lot ++ `ctorIdx, ``Lot, [mkRawNatLit 0, mkRawNatLit 1], false),
      (``Raw ++ `ctorIdx, ``Raw, [mkRawNatLit 0, mkRawNatLit 1], true),
      (`SoftwareChallengeReadTests.Fixtures.CoreSpec.Forged.natCtorIdx, ``Nat,
        [mkRawNatLit 0, .lam `n nat (mkRawNatLit 1) .default], true)] do
    let self := mkConst datatype
    let type := Expr.forallE `x self nat .default
    let read := if readsTag then mkApp2 (mkConst ``getObjTagNat [1]) self (.bvar 0) else mkRawNatLit 7
    addAndCompile <| .defnDecl {
      name := ctorIdx.str "_impl", levelParams := [], type, value := .lam `x self read .default, hints := .opaque,
      safety := .unsafe }
    let cases := mkAppN (mkConst (mkCasesOnName datatype) [1])
      (#[.lam `x self nat .default, .bvar 0] ++ alternatives.toArray)
    let index := Declaration.defnDecl {
      name := ctorIdx, levelParams := [], type, value := .lam `x self cases .default, hints := .abbrev,
      safety := .safe }
    addDecl index
    setImplementedBy ctorIdx (ctorIdx.str "_impl")
    compileDecl index

end SoftwareChallengeReadTests.Fixtures.CoreSpec.Forged

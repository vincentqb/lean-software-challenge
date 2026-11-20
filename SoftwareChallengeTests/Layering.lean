module

meta import SoftwareChallenge.CoreCode.Layering

namespace SoftwareChallengeTests.Layering

open Lean SoftwareChallenge

meta section

def layered : Project :=
  { modules := #[(`S, .coreSpec), (`P, .worldSpec), (`C, .coreCode), (`W, .worldCode), (`T, .tooling)] }

def importing (source target : Name) (comptime : Bool := false) : ModuleFact :=
  { name := source, file := s!"{source}.lean", usesModuleSystem := true,
    imports := #[{ name := target, comptime, line := 1 }] }

def pureIn (module : Name) : DeclarationFact :=
  { name := module ++ `pure, module, line := 1, computational := true, isUnsafe := false, isPartial := false,
    external := false, unfoldable := true, replaced := false, initializes := false, effects := false,
    debug := false, axioms := #[] }

def impureIn (module : Name) : DeclarationFact :=
  { pureIn module with isUnsafe := true, isPartial := true, external := true, replaced := true,
                       initializes := true, effects := true, debug := true }

def externIn (module : Name) : DeclarationFact :=
  { pureIn module with external := true, unfoldable := false, effects := true }

def constructorIn (module : Name) : DeclarationFact :=
  { pureIn module with name := module ++ `Side.right, computational := false, unfoldable := false }

def ofModules (facts : Array ModuleFact) : Inventory := { modules := facts, declarations := #[] }

def ofDeclarations (facts : Array DeclarationFact) : Inventory := { modules := #[], declarations := facts }

#guard layered.violations
  { modules := #[importing `C `S, importing `W `C, importing `T `W]
    declarations := #[pureIn `S, pureIn `C, pureIn `W, pureIn `T] } == #[]

#guard layered.violations (ofModules #[importing `X `S]) == #[.unplaced `X]

#guard layered.violations (ofDeclarations #[pureIn `X]) == #[.unplaced `X]

#guard layered.violations (ofModules #[{ importing `C `S with usesModuleSystem := false }]) == #[.legacy `C]

#guard layered.violations (ofModules #[importing `C `W]) == #[.forbiddenImport `C `W .coreCode]

#guard layered.violations (ofModules #[importing `C `T]) == #[.forbiddenImport `C `T .coreCode]

#guard layered.violations (ofModules #[importing `S `C]) == #[.forbiddenImport `S `C .coreSpec]

#guard layered.violations (ofModules #[importing `P `C]) == #[.forbiddenImport `P `C .worldSpec]

#guard layered.violations (ofModules #[importing `W `T]) == #[.forbiddenImport `W `T .worldCode]

#guard layered.violations (ofModules #[importing `C `W (comptime := true)]) == #[]

#guard layered.violations (ofModules #[importing `C `Lean.Data.Name]) == #[]

#guard layered.violations (ofDeclarations #[{ pureIn `T with axioms := #[``propext, `raw, ``sorryAx] }]) ==
  #[.axioms `T.pure #[`raw, ``sorryAx]]

#guard layered.violations (ofDeclarations #[impureIn `C]) ==
  #[.impure `C.pure .coreCode [.«unsafe», .«partial», .extern, .implementedBy, .initializer, .io, .debug]]

#guard layered.violations (ofDeclarations #[impureIn `W]) ==
  #[.impure `W.pure .worldCode [.«unsafe», .extern, .implementedBy]]

#guard layered.violations (ofDeclarations #[impureIn `T]) == #[]

#guard layered.violations (ofDeclarations #[{ pureIn `C with isPartial := true }]) ==
  #[.impure `C.pure .coreCode [.«partial»]]

#guard [`S, `P, `C, `W].all fun module =>
  layered.violations (ofDeclarations #[{ impureIn module with written := false }]) == #[] &&
    layered.violations (ofDeclarations #[{ impureIn module with derived := true }]) == #[]

#guard layered.violations (ofDeclarations #[{ impureIn `C with derived := true, written := false }]) == #[]

#guard layered.violations (ofDeclarations #[{ pureIn `C with written := false, axioms := #[`raw] }]) == #[]

#guard layered.violations (ofDeclarations #[{ pureIn `X with written := false }]) == #[.unplaced `X]

#guard layered.violations (ofDeclarations #[{ impureIn `C with computational := false }]) ==
  #[.impure `C.pure .coreCode [.«unsafe», .extern, .implementedBy]]

#guard layered.violations (ofDeclarations #[{ impureIn `W with computational := false }]) ==
  #[.impure `W.pure .worldCode [.«unsafe», .extern, .implementedBy]]

#guard layered.violations (ofDeclarations #[{ impureIn `P with computational := false }]) ==
  #[.impure `P.pure .worldSpec [.«unsafe», .extern, .implementedBy]]

#guard layered.violations (ofDeclarations #[{ pureIn `P with computational := false, external := true }]) ==
  #[.impure `P.pure .worldSpec [.extern]]

#guard layered.violations (ofDeclarations #[{ impureIn `T with computational := false }]) == #[]

#guard layered.violations (ofDeclarations #[{ constructorIn `S with replaced := true }]) ==
  #[.impure `S.Side.right .coreSpec [.implementedBy]]

#guard layered.violations (ofDeclarations #[{ constructorIn `C with replaced := true }]) ==
  #[.impure `C.Side.right .coreCode [.implementedBy]]

#guard layered.violations (ofDeclarations #[{ constructorIn `P with replaced := true }]) ==
  #[.impure `P.Side.right .worldSpec [.implementedBy]]

#guard layered.violations (ofDeclarations #[{ constructorIn `W with replaced := true }]) ==
  #[.impure `W.Side.right .worldCode [.implementedBy]]

#guard layered.violations (ofDeclarations #[{ constructorIn `T with replaced := true }]) == #[]

#guard layered.violations (ofDeclarations #[{ constructorIn `C with external := true }]) ==
  #[.impure `C.Side.right .coreCode [.extern]]

#guard layered.violations (ofDeclarations #[{ constructorIn `P with external := true }]) ==
  #[.impure `P.Side.right .worldSpec [.extern]]

#guard layered.violations (ofDeclarations #[{ constructorIn `W with external := true }]) ==
  #[.impure `W.Side.right .worldCode [.extern]]

#guard layered.violations (ofDeclarations #[{ pureIn `C with computational := false, isUnsafe := true }]) ==
  #[.impure `C.pure .coreCode [.«unsafe»]]

#guard layered.violations (ofDeclarations #[{ pureIn `P with computational := false, isUnsafe := true }]) ==
  #[.impure `P.pure .worldSpec [.«unsafe»]]

#guard layered.violations (ofDeclarations #[{ constructorIn `C with
  isPartial := true, initializes := true, effects := true, debug := true }]) == #[]

#guard layered.violations (ofDeclarations #[{ constructorIn `P with
  isPartial := true, initializes := true, effects := true, debug := true }]) == #[]

#guard layered.violations (ofDeclarations #[externIn `P]) == #[]

#guard layered.violations (ofDeclarations #[externIn `C]) == #[.impure `C.pure .coreCode [.extern, .io]]

#guard layered.violations (ofDeclarations #[externIn `W]) == #[.impure `W.pure .worldCode [.extern]]

#guard layered.violations (ofDeclarations #[{ externIn `P with unfoldable := true }]) ==
  #[.impure `P.pure .worldSpec [.unfoldableExtern]]

#guard layered.violations (ofDeclarations #[{ pureIn `P with effects := true }]) ==
  #[.impure `P.pure .worldSpec [.io]]

#guard layered.violations (ofDeclarations #[{ pureIn `C with isUnsafe := true, axioms := #[`raw] }]) ==
  #[.axioms `C.pure #[`raw], .impure `C.pure .coreCode [.«unsafe»]]

end

end SoftwareChallengeTests.Layering

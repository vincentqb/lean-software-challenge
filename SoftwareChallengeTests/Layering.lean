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

def copyIn (module : Name) : DeclarationFact :=
  { pureIn module with name := module ++ `pure._unsafe_rec, isPartial := true, written := false,
                       copyOf := some (module ++ `pure) }

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

#guard layered.violations (ofDeclarations #[{ copyIn `C with copyOfInstanceMethod := true }]) == #[]

#guard layered.violations (ofDeclarations #[{ copyIn `S with copyOfInstanceMethod := true }]) == #[]

#guard layered.violations (ofDeclarations #[{ copyIn `C with copyOfTotal := true }]) == #[]

#guard layered.violations (ofDeclarations #[{ copyIn `C with copyOfFixpoint := true, copyOfTerminated := true }]) ==
  #[]

#guard layered.violations (ofDeclarations #[{ copyIn `C with copyOfFixpoint := true }]) ==
  #[.impure `C.pure._unsafe_rec .coreCode [.«partial»]]

#guard layered.violations (ofDeclarations #[copyIn `C]) == #[.impure `C.pure._unsafe_rec .coreCode [.«partial»]]

#guard layered.violations (ofDeclarations #[{ copyIn `C with copyOfInstanceMethod := true, written := true }]) ==
  #[.impure `C.pure._unsafe_rec .coreCode [.«partial»]]

#guard layered.violations (ofDeclarations #[{ impureIn `C with computational := false }]) == #[]

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

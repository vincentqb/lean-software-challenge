module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Forged

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def forged : Name := `SoftwareChallengeReadTests.Fixtures.CoreSpec.Forged

def factOf (inventory : Inventory) (name : Name) : IO DeclarationFact :=
  match declarationNamed? inventory forged (forged ++ name) with
  | some fact => pure fact
  | none => throw <| .userError s!"{name} of {forged} is missing from the inventory"

run_cmd Elab.Command.liftCoreM do
  let lake ← lakeOf #[forged]
  let imported ← catalogEnv lake .anonymous .lint
  let modules ← catalogModules lake #[forged] imported .lint
  let inventory := (← runIn imported.env (inventoryFacts modules #[])).inventory
  let index ← factOf inventory `Side.ctorIdx
  let read ← factOf inventory ((`Side.ctorIdx).str "_impl")
  let empty ← factOf inventory `Void.ctorIdx
  check (!index.written && index.replaced && index.indexOf == some (forged ++ `Side) &&
      index.indexedConstructors == 2 && !index.indexedBuiltin && index.implementationTyped &&
      index.implementationReadsTag && !read.written && read.isUnsafe && read.readsTag &&
      empty.indexOf == some (forged ++ `Void) && empty.indexedConstructors == 0 && empty.implementationReadsTag)
    s!"the constructor index Lean generates and the tag read that implements it were misread: {repr index}, \
      {repr read}, {repr empty}"
  let written ← factOf inventory `Coin.ctorIdx
  check (written.written && written.indexOf == some (forged ++ `Coin) && written.implementationTyped &&
      written.implementationReadsTag && (← factOf inventory ((`Coin.ctorIdx).str "_impl")).readsTag)
    s!"a hand-written constructor index and tag read were misread: {repr written}"
  let natural ← factOf inventory `natCtorIdx
  check ((← factOf inventory `Box.ctorIdx).indexedConstructors == 1 &&
      (← factOf inventory `Die.ctorIdx).indexOf.isNone && (← factOf inventory `Raw.ctorIdx).indexOf.isNone &&
      natural.indexedConstructors == 2 && natural.indexedBuiltin && natural.implementationReadsTag &&
      !(← factOf inventory `Lot.ctorIdx).implementationReadsTag &&
      !(← factOf inventory ((`Lot.ctorIdx).str "_impl")).readsTag)
    "a constructor index or tag read that a command forged was read as Lean's"
  let impure := ((lake.project.violations inventory).filterMap fun
    | .impure declaration _ reasons => some (toString (declaration.replacePrefix forged .anonymous), reasons)
    | _ => none).qsort (·.1 < ·.1)
  check (impure == #[("Box.ctorIdx", [.implementedBy]), ("Coin.ctorIdx", [.implementedBy]),
      ("Coin.ctorIdx._impl", [.«unsafe»]), ("Die.ctorIdx", [.implementedBy]), ("Lot.ctorIdx", [.implementedBy]),
      ("Lot.ctorIdx._impl", [.«unsafe»]), ("Raw.ctorIdx", [.implementedBy]), ("natCtorIdx", [.implementedBy])])
    s!"the CoreSpec role table did not admit exactly Lean's constructor index and its tag read: {repr impure}"

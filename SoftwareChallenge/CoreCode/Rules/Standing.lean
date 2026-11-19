module

public import SoftwareChallenge.CoreCode.Facts

public section

namespace SoftwareChallenge

open Lean

inductive Standing where
  | holds (module : Name)
  | unsound (module : Name)
  | absent
  | outside (module : Name) (importsSolution : Bool)
  | kind (module : Name) (found : ConstantKind)
  | universes (module : Name) (found : List Name)
  | differs (module : Name) (plain explicit : String)
  | auxiliary (module : Name) (constant : Name)
  deriving BEq, Repr, Inhabited

end SoftwareChallenge

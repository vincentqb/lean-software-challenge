module

public meta import Lean.Data.Json
public meta import SoftwareChallenge.CoreCode.Facts

public section
meta section

open Lean

namespace SoftwareChallenge

deriving instance ToJson, FromJson for Place
deriving instance ToJson, FromJson for SourceFact
deriving instance ToJson, FromJson for PackageFact
deriving instance ToJson, FromJson for OwnTestKind
deriving instance ToJson, FromJson for OwnTestFact
deriving instance ToJson, FromJson for LakeFacts

namespace Read

def renderLake (lake : LakeFacts) : String := (toJson lake).pretty

def parseLake (text : String) : Except String LakeFacts := do
  fromJson? (← Json.parse text)

def loadLake (path : System.FilePath) : IO LakeFacts := do
  let text ← try IO.FS.readFile path catch failure =>
    throw <| .userError s!"{path}: the step cannot read it ({failure}), so it does not know the package's modules, \
      files, and settings. `lake build` writes it; run `lake build`, then run the step again."
  match parseLake text with
  | .ok lake => return lake
  | .error problem =>
    throw <| .userError s!"{path}: it is not the JSON object of Lake facts that `lake build` writes ({problem}), \
      so the step does not know the package's modules, files, and settings. Delete {path} and run `lake build` to \
      write it again, then run the step again."

end SoftwareChallenge.Read

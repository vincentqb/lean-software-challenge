module

public meta import Lean

public section
meta section

open Lean

namespace SoftwareChallenge.Read

def oneLine (text : String) : String :=
  " ".intercalate ((text.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty))

def lineAt (source : String) (line : Nat) : String :=
  (((source.splitOn "\n")[line - 1]?).map (·.trimAscii.toString)).getD ""

def textAt (source : String) (range : DeclarationRange) : String :=
  if range.pos.line != range.endPos.line then "" else
    match (source.splitOn "\n")[range.pos.line - 1]? with
    | some line => String.ofList ((line.toList.drop range.pos.column).take (range.endPos.column - range.pos.column))
    | none => ""

private def signatureEnd : List Char → Nat → List Char → Option (List Char)
  | ':' :: '=' :: _, 0, kept => some kept.reverse
  | char :: rest, depth, kept =>
    signatureEnd rest (if "([{⦃⟨".contains char then depth + 1 else if ")]}⦄⟩".contains char then depth - 1
      else depth) (char :: kept)
  | [], _, _ => none

def signatureAt (source : String) (position : Position) : String :=
  let lines := source.splitOn "\n"
  match lines[position.line - 1]? with
  | some first =>
    let text := "\n".intercalate (String.ofList (first.toList.drop position.column) :: lines.drop position.line)
    ((signatureEnd text.toList 0 []).map fun chars => oneLine (String.ofList chars)).getD ""
  | none => ""

def namespaceOf (full : Name) (written : String) : Name :=
  let whole := full.components
  let tail := written.toName.components
  if !tail.isEmpty && tail.length ≤ whole.length && whole.drop (whole.length - tail.length) == tail then
    (whole.take (whole.length - tail.length)).foldl (· ++ ·) .anonymous
  else .anonymous

def ownerOf (name : Name) : Name :=
  let user := privateToUserName name
  let kept := (user.components.takeWhile (!·.isInternalOrNum)).foldl (· ++ ·) .anonymous
  let kept := if kept.isAnonymous then user else kept
  match privatePrefix? name with
  | some prefixName => prefixName ++ kept
  | none => kept

def rangesIn (env : Environment) (index : ModuleIdx) (name : Name) : Option DeclarationRanges :=
  let find := fun (level : OLeanLevel) =>
    ((declRangeExt.toPersistentEnvExtension.getModuleEntries env index (level := level)).binSearch (name, default)
      (fun a b => Name.quickLt a.1 b.1)).map (·.2)
  (find .exported).orElse fun _ => find .server

def moduleOf? (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).map fun index => env.header.moduleNames[index.toNat]!

def moduleData? (env : Environment) (module : Name) : Option (ModuleIdx × ModuleData) := do
  let index ← env.getModuleIdx? module
  return (index, env.header.moduleData[index.toNat]!)

end SoftwareChallenge.Read

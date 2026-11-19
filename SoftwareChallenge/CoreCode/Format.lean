module

public import SoftwareChallenge.CoreSpec.Format
import SoftwareChallenge.CoreCode.Doc

public section

namespace SoftwareChallenge

open Lean

private def Name.chars : Name → List Char
  | .anonymous => []
  | .str .anonymous component => component.toList
  | .str parent component => Name.chars parent ++ '.' :: component.toList
  | .num .anonymous index => (toString index).toList
  | .num parent index => Name.chars parent ++ '.' :: (toString index).toList

private def Name.ofChars (parent : Name) (component : List Char) : List Char → Name
  | [] => .str parent (String.ofList component.reverse)
  | char :: rest =>
    if char = '.' then Name.ofChars (.str parent (String.ofList component.reverse)) [] rest
    else Name.ofChars parent (char :: component) rest

private def Name.text (name : Name) : String :=
  String.ofList (Name.chars name)

private def Name.ofText (text : String) : Name :=
  Name.ofChars .anonymous [] text.toList

def Config.render (config : Config) : String :=
  Doc.render ⟨[("challenge_module", .string (Name.text config.challenge)),
    ("solution_module", .string (Name.text config.solution)),
    ("theorem_names", .array (config.theorems.toList.map Name.text)),
    ("definition_names", .array (config.definitions.toList.map Name.text)),
    ("permitted_axioms", .array (config.axioms.toList.map Name.text))]⟩

def Config.parse (text : String) : Option Config := do
  let [("challenge_module", .string challenge), ("solution_module", .string solution),
      ("theorem_names", .array theorems), ("definition_names", .array definitions),
      ("permitted_axioms", .array axioms)] := (← Doc.parse text).fields | none
  return {
    challenge := Name.ofText challenge
    solution := Name.ofText solution
    theorems := (theorems.map Name.ofText).toArray
    definitions := (definitions.map Name.ofText).toArray
    axioms := (axioms.map Name.ofText).toArray }

def Lock.render (entries : Array Lock.Entry) : String :=
  Doc.render ⟨entries.toList.map fun entry => (entry.path, .string entry.digest)⟩

private def Lock.entryOf : String × Doc.Value → Option Lock.Entry
  | (path, .string digest) => some { path, digest }
  | (_, .array _) => none

def Lock.parse (text : String) : Option (Array Lock.Entry) := do
  return (← (← Doc.parse text).fields.mapM Lock.entryOf).toArray

private def Lock.distinct (seen : List String) : List String → List String
  | [] => []
  | path :: rest => if path ∈ seen then Lock.distinct seen rest else path :: Lock.distinct (path :: seen) rest

private def Lock.violation (path : String) : Option String → Option String → Option Lock.Violation
  | none, none => none
  | none, some _ => some (.unrecorded path)
  | some _, none => some (.missing path)
  | some recorded, some found => if recorded = found then none else some (.differs path)

def Lock.violations (locked current : Array Lock.Entry) : Array Lock.Violation :=
  ((Lock.distinct [] ((current ++ locked).toList.map (·.path))).filterMap fun path =>
    Lock.violation path (Lock.digestOf locked path) (Lock.digestOf current path)).toArray

end SoftwareChallenge

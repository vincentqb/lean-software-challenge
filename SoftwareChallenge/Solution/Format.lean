module

public import SoftwareChallenge.CoreCode.Format
import all SoftwareChallenge.CoreCode.Format
import SoftwareChallenge.CoreCode.Doc

public section

namespace SoftwareChallenge

open Lean

private theorem Name.PlainComponent.undotted {component : String} (plain : Name.PlainComponent component) :
    ∀ char ∈ component.toList, char ≠ '.' := by
  unfold Name.PlainComponent at plain
  split at plain
  · exact plain.elim
  · rename_i first rest split
    intro char member
    rw [split] at member
    exact (plain.2 char member).1

private theorem Name.ofChars_append {parent : Name} {component chars : List Char} (rest : List Char)
    (undotted : ∀ char ∈ chars, char ≠ '.') :
    Name.ofChars parent component (chars ++ rest) = Name.ofChars parent (chars.reverse ++ component) rest := by
  induction chars generalizing component with
  | nil => rfl
  | cons char chars ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at undotted
    simp [Name.ofChars, undotted.1, ih undotted.2]

private theorem Name.chars_str {parent : Name} (named : parent ≠ .anonymous) (component : String) :
    Name.chars (.str parent component) = Name.chars parent ++ '.' :: component.toList := by
  cases parent with
  | anonymous => exact absurd rfl named
  | str => rfl
  | num => rfl

private theorem Name.ofChars_chars {name : Name} (plain : Name.Plain name) :
    (∀ rest, Name.ofChars .anonymous [] (Name.chars name ++ '.' :: rest) = Name.ofChars name [] rest) ∧
      Name.ofChars .anonymous [] (Name.chars name) = name := by
  induction name with
  | anonymous => exact plain.elim
  | num => exact plain.elim
  | str parent component ih =>
    obtain ⟨parentPlain, componentPlain⟩ := plain
    have undotted := componentPlain.undotted
    rcases parentPlain with rfl | parentPlain
    · refine ⟨fun rest => ?_, ?_⟩
      · rw [Name.chars, Name.ofChars_append _ undotted]
        simp [Name.ofChars]
      · rw [Name.chars, ← List.append_nil component.toList, Name.ofChars_append _ undotted]
        simp [Name.ofChars]
    · have named : parent ≠ .anonymous := by
        rintro rfl
        exact parentPlain
      refine ⟨fun rest => ?_, ?_⟩
      · rw [Name.chars_str named, List.append_assoc, List.cons_append, (ih parentPlain).1,
          Name.ofChars_append _ undotted]
        simp [Name.ofChars]
      · rw [Name.chars_str named, (ih parentPlain).1, ← List.append_nil component.toList,
          Name.ofChars_append _ undotted]
        simp [Name.ofChars]

private theorem Name.ofText_text {name : Name} (plain : Name.Plain name) : Name.ofText (Name.text name) = name := by
  rw [Name.ofText, Name.text, String.toList_ofList]
  exact (Name.ofChars_chars plain).2

private theorem Name.ofText_texts {names : Array Name} (plain : ∀ name ∈ names, Name.Plain name) :
    (names.toList.map (Name.ofText ∘ Name.text)).toArray = names := by
  conv => rhs; rw [← Array.toArray_toList (xs := names), ← List.map_id names.toList]
  congr 1
  exact List.map_congr_left fun name member => Name.ofText_text (plain name (Array.mem_toList_iff.mp member))

theorem Config.parse_render (config : Config) (plain : config.Plain) :
    Config.parse (Config.render config) = some config := by
  obtain ⟨challenge, solution, theorems, definitions, axioms⟩ := config
  obtain ⟨challengePlain, solutionPlain, theoremsPlain, definitionsPlain, axiomsPlain⟩ := plain
  simp only [Config.parse, Config.render, Doc.parse_render]
  simp [Name.ofText_text challengePlain, Name.ofText_text solutionPlain, Name.ofText_texts theoremsPlain,
    Name.ofText_texts definitionsPlain, Name.ofText_texts axiomsPlain]

theorem Config.parse_render_rejects_refusing :
    ¬ ∀ (config : Config), config.Plain →
      (fun (_ : String) => (none : Option Config)) (Config.render config) = some config := by
  intro refusing
  have plain : Config.Plain ⟨`Challenge, `Solution, #[], #[], #[]⟩ := by
    simp [Config.Plain, Name.Plain, Name.PlainComponent, Name.PlainCharacter]
  exact absurd (refusing _ plain) (by simp)

private theorem Lock.entries_mapM (entries : List Lock.Entry) :
    entries.mapM (Lock.entryOf ∘ fun entry => (entry.path, Doc.Value.string entry.digest)) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp [List.mapM_cons, Lock.entryOf, ih]

theorem Lock.parse_render (entries : Array Lock.Entry) : Lock.parse (Lock.render entries) = some entries := by
  simp [Lock.parse, Lock.render, Doc.parse_render, Lock.entries_mapM]

theorem Lock.parse_render_rejects_refusing :
    ¬ ∀ (entries : Array Lock.Entry),
      (fun (_ : String) => (none : Option (Array Lock.Entry))) (Lock.render entries) = some entries := by
  intro refusing
  exact absurd (refusing #[]) (by simp)

private theorem Lock.mem_distinct {seen paths : List String} {path : String} :
    path ∈ Lock.distinct seen paths ↔ path ∉ seen ∧ path ∈ paths := by
  induction paths generalizing seen with
  | nil => simp [Lock.distinct]
  | cons first rest ih =>
    by_cases recorded : first ∈ seen <;> simp only [Lock.distinct, recorded, ↓reduceIte, ih, List.mem_cons] <;> grind

private theorem Lock.violation_eq_none {path : String} {recorded found : Option String} :
    Lock.violation path recorded found = none ↔ recorded = found := by
  cases recorded <;> cases found <;> simp [Lock.violation]

private theorem Lock.digestOf_eq_none {entries : Array Lock.Entry} {path : String} :
    Lock.digestOf entries path = none ↔ ∀ entry ∈ entries, entry.path ≠ path := by
  simp [Lock.digestOf, Array.find?_eq_none]

theorem Lock.violations_eq_empty_iff (locked current : Array Lock.Entry) :
    Lock.violations locked current = #[] ↔ ∀ path, Lock.digestOf locked path = Lock.digestOf current path := by
  rw [Lock.violations, List.toArray_eq_iff, Array.toList_empty, List.filterMap_eq_nil_iff]
  simp only [Lock.violation_eq_none, Lock.mem_distinct, List.not_mem_nil, not_false_eq_true, true_and, List.mem_map,
    Array.mem_toList_iff]
  constructor
  · intro agree path
    by_cases listed : ∃ entry ∈ current ++ locked, entry.path = path
    · exact agree path listed
    · simp only [Array.mem_append, not_exists, not_and] at listed
      rw [Lock.digestOf_eq_none.mpr fun entry member => listed entry (Or.inr member),
        Lock.digestOf_eq_none.mpr fun entry member => listed entry (Or.inl member)]
  · exact fun agree path _ => agree path

theorem Lock.violations_eq_empty_iff_rejects_accepting :
    ¬ ∀ (locked current : Array Lock.Entry),
      (fun (_ _ : Array Lock.Entry) => (#[] : Array Lock.Violation)) locked current = #[] ↔
      ∀ path, Lock.digestOf locked path = Lock.digestOf current path := by
  intro accepting
  have agree := (accepting #[{ path := "Challenge.lean", digest := "1" }]
    #[{ path := "Challenge.lean", digest := "2" }]).mp rfl "Challenge.lean"
  simp [Lock.digestOf] at agree

end SoftwareChallenge

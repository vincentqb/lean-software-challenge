module

meta import SoftwareChallenge.CoreSpec.Package
meta import SoftwareChallenge.CoreCode.Format
meta import Lean.Data.Json

meta section

namespace SoftwareChallengeTests.Format

open Lean SoftwareChallenge

def constantFolding : Config where
  challenge := `Challenge
  solution := `ConstantFolding.Solution
  theorems :=
    #[`ConstantFolding.fold_preserves_meaning, `ConstantFolding.fold_closed_literal, `ConstantFolding.fold_normalizes,
      `ConstantFolding.fold_idempotent, `ConstantFolding.fold_keeps_literal, `ConstantFolding.output_correct,
      `ConstantFolding.fold_preserves_meaning_rejects_constant, `ConstantFolding.fold_closed_literal_rejects_identity,
      `ConstantFolding.fold_normalizes_rejects_identity, `ConstantFolding.fold_idempotent_rejects_increment,
      `ConstantFolding.fold_keeps_literal_rejects_zero, `ConstantFolding.fold_keeps_literal_applies,
      `ConstantFolding.output_correct_rejects_suffix]
  definitions := #[`ConstantFolding.fold, `ConstantFolding.output]
  axioms := standardAxioms

def constantFoldingComparator : String := r#"{
  "challenge_module": "Challenge",
  "solution_module": "ConstantFolding.Solution",
  "theorem_names": [
    "ConstantFolding.fold_preserves_meaning",
    "ConstantFolding.fold_closed_literal",
    "ConstantFolding.fold_normalizes",
    "ConstantFolding.fold_idempotent",
    "ConstantFolding.fold_keeps_literal",
    "ConstantFolding.output_correct",
    "ConstantFolding.fold_preserves_meaning_rejects_constant",
    "ConstantFolding.fold_closed_literal_rejects_identity",
    "ConstantFolding.fold_normalizes_rejects_identity",
    "ConstantFolding.fold_idempotent_rejects_increment",
    "ConstantFolding.fold_keeps_literal_rejects_zero",
    "ConstantFolding.fold_keeps_literal_applies",
    "ConstantFolding.output_correct_rejects_suffix"
  ],
  "definition_names": [
    "ConstantFolding.fold",
    "ConstantFolding.output"
  ],
  "permitted_axioms": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
"#

#guard Config.render constantFolding == constantFoldingComparator

#guard Config.parse constantFoldingComparator == some constantFolding

def slowKills : Config where
  challenge := `Challenge
  solution := `SlowKills.Solution
  theorems := #[`SlowKills.double_correct, `SlowKills.triple_correct, `SlowKills.double_correct_rejects_identity,
    `SlowKills.triple_correct_rejects_identity]
  definitions := #[`SlowKills.double, `SlowKills.triple]
  axioms := standardAxioms

def slowKillsComparator : String := r#"{
  "challenge_module": "Challenge",
  "solution_module": "SlowKills.Solution",
  "theorem_names": [
    "SlowKills.double_correct",
    "SlowKills.triple_correct",
    "SlowKills.double_correct_rejects_identity",
    "SlowKills.triple_correct_rejects_identity"
  ],
  "definition_names": [
    "SlowKills.double",
    "SlowKills.triple"
  ],
  "permitted_axioms": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
"#

#guard Config.render slowKills == slowKillsComparator

#guard Config.parse slowKillsComparator == some slowKills

def softwareChallenge : Config where
  challenge := `SoftwareChallengeStatement.Challenge
  solution := `SoftwareChallenge.Solution
  theorems :=
    #[`SoftwareChallenge.layering_sound, `SoftwareChallenge.layering_sound_rejects_accepting,
      `SoftwareChallenge.layering_sound_applies, `SoftwareChallenge.purity_sound,
      `SoftwareChallenge.purity_sound_rejects_accepting, `SoftwareChallenge.purity_sound_applies,
      `SoftwareChallenge.Shape.witnesses?_sound, `SoftwareChallenge.Shape.witnesses?_sound_rejects_accepting,
      `SoftwareChallenge.Shape.witnesses?_sound_applies, `SoftwareChallenge.Shape.witnesses?_complete,
      `SoftwareChallenge.Shape.witnesses?_complete_rejects_refusing, `SoftwareChallenge.Shape.isKill_sound,
      `SoftwareChallenge.Shape.isKill_sound_rejects_accepting, `SoftwareChallenge.Shape.isKill_sound_applies,
      `SoftwareChallenge.Shape.isKill_complete, `SoftwareChallenge.Shape.isKill_complete_rejects_refusing,
      `SoftwareChallenge.Shape.independent_sound, `SoftwareChallenge.Shape.independent_sound_rejects_accepting,
      `SoftwareChallenge.Shape.independent_sound_applies, `SoftwareChallenge.Shape.independent_complete,
      `SoftwareChallenge.Shape.independent_complete_rejects_refusing, `SoftwareChallenge.Shape.ofExpr_eq_iff,
      `SoftwareChallenge.Shape.ofExpr_eq_iff_rejects_constant, `SoftwareChallenge.Graph.closure_sound,
      `SoftwareChallenge.Graph.closure_sound_rejects_extra_node, `SoftwareChallenge.Graph.closure_sound_applies,
      `SoftwareChallenge.Graph.closure_complete, `SoftwareChallenge.Graph.closure_complete_rejects_roots_only,
      `SoftwareChallenge.Config.parse_render, `SoftwareChallenge.Config.parse_render_rejects_refusing,
      `SoftwareChallenge.Lock.parse_render, `SoftwareChallenge.Lock.parse_render_rejects_refusing,
      `SoftwareChallenge.Lock.violations_eq_empty_iff,
      `SoftwareChallenge.Lock.violations_eq_empty_iff_rejects_accepting,
      `SoftwareChallenge.Grade.decide_eq_accept_iff, `SoftwareChallenge.Grade.decide_eq_accept_iff_rejects_accepting,
      `SoftwareChallenge.Grade.decide_eq_first, `SoftwareChallenge.Grade.decide_eq_first_rejects_refusing]
  definitions :=
    #[`SoftwareChallenge.Project.violations, `SoftwareChallenge.Shape.witnesses?, `SoftwareChallenge.Shape.isKill,
      `SoftwareChallenge.Shape.independent, `SoftwareChallenge.Shape.ofExpr, `SoftwareChallenge.Graph.closure,
      `SoftwareChallenge.Config.render, `SoftwareChallenge.Config.parse, `SoftwareChallenge.Lock.render,
      `SoftwareChallenge.Lock.parse, `SoftwareChallenge.Lock.violations, `SoftwareChallenge.Grade.decide]
  axioms := standardAxioms

def legacyComparatorJson (config : Config) : String :=
  let quoted := fun (name : Name) => (toJson name).compress
  let names := fun (names : Array Name) => if names.isEmpty then "[]" else
    "[\n" ++ ",\n".intercalate (names.map (s!"    {quoted ·}")).toList ++ "\n  ]"
  let fields := [("challenge_module", quoted config.challenge), ("solution_module", quoted config.solution),
    ("theorem_names", names config.theorems), ("definition_names", names config.definitions),
    ("permitted_axioms", names config.axioms)]
  "{\n" ++ ",\n".intercalate (fields.map fun (key, value) => s!"  \"{key}\": {value}") ++ "\n}\n"

#guard [constantFolding, slowKills, softwareChallenge, { slowKills with theorems := #[], definitions := #[] }].all
  fun config => Config.render config == legacyComparatorJson config

def lakeReads (config : Config) : Bool :=
  match Json.parse (Config.render config) with
  | .error _ => false
  | .ok json =>
    let name := fun (key : String) => (json.getObjValAs? String key).toOption.map String.toName
    let names := fun (key : String) => (json.getObjValAs? (Array String) key).toOption.map (·.map String.toName)
    name "challenge_module" == some config.challenge && name "solution_module" == some config.solution &&
      names "theorem_names" == some config.theorems && names "definition_names" == some config.definitions &&
      names "permitted_axioms" == some config.axioms

#guard lakeReads constantFolding

#guard lakeReads softwareChallenge

#guard Config.parse (Config.render softwareChallenge) == some softwareChallenge

#guard Config.parse "{\"solution_module\": \"S\", \"challenge_module\": \"C\", \"theorem_names\": [],
  \"definition_names\": [], \"permitted_axioms\": []}" == none

def awkward : Array Lock.Entry := #[
  { path := "lakefile.lean", digest := "14750095111711872102" },
  { path := "My Challenge/Core Spec.lean", digest := "1" },
  { path := "quoted \"name\" and back\\slash.lean", digest := "2" },
  { path := "line\nfeed, tab\t, return\r, bell\x07, é and 😀", digest := "3" }]

#guard Lock.parse (Lock.render awkward) == some awkward

#guard match Json.parse (Lock.render awkward) with
  | .ok json => awkward.all fun entry => (json.getObjValAs? String entry.path).toOption == some entry.digest
  | .error _ => false

#guard awkward.all fun entry => Lock.render #[entry] ==
  "{\n  " ++ (Json.str entry.path).compress ++ ": " ++ (Json.str entry.digest).compress ++ "\n}\n"

#guard Lock.render (awkward.extract 0 2) == r#"{
  "lakefile.lean": "14750095111711872102",
  "My Challenge/Core Spec.lean": "1"
}
"#

#guard Lock.render #[] == "{}\n" && Lock.parse "{}\n" == some #[]

#guard Lock.parse "14750095111711872102 lakefile.lean\n18062915072279311825 lake-manifest.json" == none

#guard Lock.parse r#"{"Challenge.lean": ["4606896722634636308"]}"# == none

#guard Lock.parse "\t{ \"a\" :\"1\",\r\n\"b\\u0041\\/\":\"2\" }" ==
  some #[{ path := "a", digest := "1" }, { path := "bA/", digest := "2" }]

def locked : Array Lock.Entry :=
  #[{ path := "a", digest := "1" }, { path := "b", digest := "2" }, { path := "c", digest := "3" }]

#guard Lock.violations locked locked == #[]

#guard Lock.violations locked #[{ path := "a", digest := "1" }, { path := "b", digest := "9" },
  { path := "d", digest := "4" }] == #[.differs "b", .unrecorded "d", .missing "c"]

#guard Lock.violations #[{ path := "a", digest := "1" }, { path := "a", digest := "2" }]
  #[{ path := "a", digest := "1" }] == #[]

#guard Lock.violations #[{ path := "a", digest := "2" }, { path := "a", digest := "1" }]
  #[{ path := "a", digest := "1" }] == #[.differs "a"]

#guard Lock.violations #[] #[{ path := "a", digest := "1" }, { path := "a", digest := "1" }] ==
  #[.unrecorded "a"]

end SoftwareChallengeTests.Format

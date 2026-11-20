module

meta import SoftwareChallengeReadTests.Support
meta import SoftwareChallenge.Steps.Replay

namespace SoftwareChallengeReadTests.Challenge

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def lastNames (names : Array Name) : Array String := names.map fun name => name.componentsRev.head!.toString

def binder (kind : BinderKind) (prop mentions : Bool) (refers : List Nat) : Binder := { kind, prop, mentions, refers }

def headline (challenge : ChallengeFacts) (name : Name) : IO HeadlineFact :=
  match headlineNamed? challenge name with
  | some found => pure found
  | none => throw <| .userError s!"{name} is not a headline of {challenge.module}"

run_cmd Elab.Command.liftCoreM do
  let member := fun (name : Name) => fixture (`Challenge ++ name)
  let challenge ← challengeNamed (fixture `Challenge)
  check (challenge.module == fixture `Challenge && challenge.file == "SoftwareChallengeTests/Fixtures/Challenge.lean")
    "the challenge's module or file was misread"
  check (lastNames (challenge.headlines.map (·.target.constant.name)) ==
      #["double_even", "double_zero", "double_one", "double_one_rejects_one"])
    s!"the headlines were misread: {challenge.headlines.map (·.target.constant.name)}"
  check (challenge.kills.map (fun kill => (kill.target.constant.name, kill.headline, kill.target.place.line)) ==
      #[(member `double_even_rejects_identity, member `double_even, 18),
        (member `double_even_rejects_nothing, member `double_even, 20),
        (member `double_even_independent, member `double_even, 22),
        (member `double_even_partly_independent, member `double_even, 26),
        (member `double_even_independent_mixed, member `double_even, 30),
        (member `double_even_rejects_itself, member `double_even, 34),
        (member `triple_rejects_nothing, member `triple, 36)])
    s!"the kills were misread: {challenge.kills.map (·.target.constant.name)}"
  check (challenge.holes.map (·.constant.name) == #[member `double] && challenge.replaceable == #[member `double])
    "the holes were misread"
  check (challenge.filled.map (fun (name, place) => (name, place.line)) == #[(member `triple, 14)] &&
      challenge.axioms.isEmpty) "the filled definitions were misread"
  check (challenge.terminating.map (fun found => (found.definition, found.headline, found.place.line)) ==
      #[(member `triple, member `double_zero, 38)]) "the termination headlines were misread"
  check (challenge.runtimeImports.any (·.text == "public import SoftwareChallengeTests.Fixtures.CoreCode") &&
      challenge.metaImports.any fun line => line.fact.name == `SoftwareChallenge && line.fact.line == 4)
    "the challenge's runtime and meta imports were misread"
  check (challenge.closure.contains (fixture `CoreCode) && challenge.closure.contains (fixture `CoreSpec) &&
      challenge.closure.contains `SoftwareChallenge.Commands && !challenge.closure.contains challenge.module)
    "the challenge's import closure, of every import kind, was misread"
  let doubleEven ← headline challenge (member `double_even)
  check (doubleEven.target.signature == "(n : Nat) : double n % 2 = 0" && doubleEven.target.written == "double_even" &&
      doubleEven.target.enclosingNamespace == fixture `Challenge && doubleEven.target.place.line == 16)
    s!"a headline's signature, written name, namespace, or line was misread: {doubleEven.target.signature}"
  check (challenge.holes.all fun hole => hole.signature == ": Nat → Nat" && hole.constant.kind == .defined .safe)
    "a hole's signature or kind was misread"
  check (doubleEven.target.rendered == "∀ (n : Nat), SoftwareChallengeTests.Fixtures.Challenge.double n % 2 = 0" &&
      contains doubleEven.target.renderedExplicit "@HMod.hMod")
    s!"a headline was rendered otherwise: {doubleEven.target.rendered} {doubleEven.target.renderedExplicit}"
  let zero ← headline challenge (member `double_zero)
  check (zero.killTemplate? == some "¬?wrong_double 0 = 0" && zero.telescope.isEmpty)
    s!"a kill template was misread: {zero.killTemplate?}"
  check ((← headline challenge (member `double_one_rejects_one)).killTemplate?.isNone)
    "a headline that mentions no hole got a kill template"

run_cmd Elab.Command.liftCoreM do
  let member := fun (name : Name) => fixture (`WitnessChallenge ++ name)
  let challenge ← challengeNamed (fixture `WitnessChallenge)
  check (lastNames (challenge.headlines.map (·.target.constant.name)) == #["double_halves", "double_positive",
      "double_between", "double_lengths", "succ_hits_one", "double_small", "double_zero", "double_negative_vanishes",
      "double_nonnegative_vanishes", "double_vanishes_only_at_zero", "double_zero_fin", "double_first", "double_fin",
      "double_under_claim", "double_at", "double_assumes_wrapped", "double_hidden", "double_odd", "succ_law"])
    s!"a kill or a witness was read as a headline: {challenge.headlines.map (·.target.constant.name)}"
  let derived := [(`double_halves, "∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n = 4", 16),
    (`double_positive, "∃ n, 0 < SoftwareChallengeTests.Fixtures.WitnessChallenge.double n", 21),
    (`double_between, "∃ m n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double m < \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double n ∧ \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double n < 10", 29),
    (`double_lengths, "∃ α xs, xs.length = SoftwareChallengeTests.Fixtures.WitnessChallenge.double 1", 34),
    (`succ_hits_one, "SoftwareChallengeTests.Fixtures.SuccAgrees SoftwareChallengeTests.Fixtures.nativeSucc → ∃ n, \
      SoftwareChallengeTests.Fixtures.nativeSucc n = 1", 39),
    (`double_negative_vanishes, "∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n < 0", 52),
    (`double_zero_fin, "∃ n inst, SoftwareChallengeTests.Fixtures.WitnessChallenge.double ↑0 = 0", 67),
    (`double_first, "∃ n h, ↑⟨0, h⟩ = 0", 72), (`double_fin, "∃ i, True", 77),
    (`double_under_claim, "(∀ (m : Nat), m > 0 → SoftwareChallengeTests.Fixtures.SuccAt m) → ∃ n, \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double n < 5", 81),
    (`double_at, "∃ n, SoftwareChallengeTests.Fixtures.SuccAt n → \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double n = 1", 86),
    (`double_hidden, "∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n = 4", 96)]
  let expected := (derived.map fun (name, statement, line) =>
    (witnessName (member name), member name, true, statement, line, s!"{name}_applies")).toArray.push
      (member `double_odd_applies, member `double_odd, false,
        "∃ n, SoftwareChallengeTests.Fixtures.WitnessChallenge.double n = 3", 101, "double_odd_applies")
  check (challenge.witnesses.map (fun witness => (witness.target.constant.name, witness.headline, witness.derived,
      witness.target.rendered, witness.target.place.line, witness.target.written)) == expected)
    s!"the witnesses were misread: {challenge.witnesses.map fun witness => (witness.target.constant.name,
      witness.target.rendered, witness.target.place.line)}"
  check (challenge.witnesses.all fun witness => witness.target.enclosingNamespace == fixture `WitnessChallenge &&
      (witness.target.signature.isEmpty == witness.derived))
    "a witness's namespace or signature was misread"
  let source ← IO.FS.readFile challenge.file
  let replayed := challenge.witnesses.map fun witness =>
    (witness.target.constant.name, SoftwareChallenge.Steps.Replay.lineOf source witness.target.constant.name,
      witness.target.place.line)
  check (replayed.all fun (_, shown, line) => shown == some s!" (Challenge.lean:{line})")
    s!"replay places a witness elsewhere than lint does: {replayed}"
  check (challenge.kills.any fun kill => kill.headline == member `double && kill.target.constant.name ==
      member `double_rejects_nothing) "a kill of a hole, which is not a headline, was not read"
  for (name, binders) in [(`double_fin, [binder .input false true []]),
      (`double_first, [binder .input false false [], binder .input true true [0],
        binder .precondition true true [0, 1]]),
      (`double_zero_fin, [binder .input false false [], binder .input true false [0],
        binder .precondition true true [0, 1]]),
      (`double_under_claim, [binder .input false false [], binder .claim true false [],
        binder .precondition true true [0]]),
      (`double_at, [binder .input false false [], binder .claim true false [0], binder .precondition true true [0]]),
      (`double_assumes_wrapped, [binder .claim true true [], binder .input false false []]),
      (`double_negative_vanishes, [binder .input false false [], binder .precondition true true [0]]),
      (`double_nonnegative_vanishes, [binder .input false false [], binder .precondition true true [0]]),
      (`double_vanishes_only_at_zero, []), (`succ_law, [binder .claim true true [], binder .input false false []])] do
    let found ← headline challenge (member name)
    check (found.binders challenge == binders)
      s!"the binders of {name} were classified as {repr (found.binders challenge)}"
  let underClaim ← headline challenge (member `double_under_claim)
  check (underClaim.claimed challenge == #[(1, fixture `SuccAt,
      "∀ (m : Nat), m > 0 → SoftwareChallengeTests.Fixtures.SuccAt m")])
    "a world claim under ∀ and → was not read as a claim"
  check ((underClaim.telescope[1]?).map (fun binder => (binder.conclusion, binder.variables)) ==
      some ("SoftwareChallengeTests.Fixtures.SuccAt m", #["m"]))
    "the peeled conclusion or variables of a claim under ∀ and → were misread"
  check (((← headline challenge (member `double_assumes_wrapped)).claimed challenge).map (·.2.1) ==
      #[fixture `SuccAgrees]) "a world claim a WorldSpec definition wraps was not read as assumed"
  check (challenge.claims.contains (fixture `SuccAgrees) && challenge.claims.contains (fixture `SuccAt))
    "the world claims of the challenge's environment were misread"
  let hidden ← headline challenge (member `double_nonnegative_vanishes)
  check (Telescope.needsWitness (hidden.binders challenge) &&
      !challenge.witnesses.any (·.headline == hidden.target.constant.name) &&
      hidden.witness? == some "∃ n, 0 ≤ SoftwareChallengeTests.Fixtures.WitnessChallenge.double n")
    "a precondition that a hidden definition holds was not read as needing a witness that no kill derived"
  check ((← headline challenge (member `double_hidden)).witness? == some ("∃ n n_1, \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double n = 4 ∧ 0 ≤ \
      SoftwareChallengeTests.Fixtures.WitnessChallenge.double n_1"))
    "the witness a hidden definition calls for was misread"
  check (challenge.replaceable == #[member `double, fixture `wrongSucc, fixture `nativeSucc])
    s!"the replaceable constants, the holes and the WorldSpec foreign functions, were misread: {challenge.replaceable}"
  check ((← headline challenge (member `succ_hits_one)).killTemplate? == some "¬(SoftwareChallengeTests.Fixtures.\
      SuccAgrees ?wrong_nativeSucc → ∀ (n : Nat), ?wrong_nativeSucc n = 1 → n = 0)")
    "a kill template that replaces a foreign function was misread"

run_cmd Elab.Command.liftCoreM do
  let member := fun (name : Name) => fixture (`KeptChallenge ++ name)
  let challenge ← challengeNamed (fixture `KeptChallenge)
  let positive ← headline challenge (member `double_positive_one)
  check (positive.binders challenge == [binder .precondition true true []] &&
      (Statement.closedHypotheses challenge positive).map (·.shown) ==
        ["0 < SoftwareChallengeTests.Fixtures.KeptChallenge.double 1"])
    "a hypothesis about a hole that mentions no input was misread"
  check (Statement.hypothesisErrors challenge == #[.unnamedHypothesis (member `double_positive_one)
      (positive.telescope[0]!)] && Statement.witnessErrors challenge == #[])
    "a hypothesis about a hole that mentions no input did not get exactly one fix"
  check ((← headline challenge (member `double_kept)).binders challenge == [binder .input false false [],
      binder .input true true [0], binder .input false true [0, 1], binder .precondition true false [0]])
    "a hypothesis a later input depends on was misread"
  check ((← headline challenge (member `double_kept_plain)).binders challenge == [binder .input false false [],
      binder .input true false [0], binder .input false false [0, 1], binder .precondition true true [0]])
    "a plain hypothesis a later input depends on was misread"
  let witnessOf := fun (headline : Name) =>
    (challenge.witnesses.find? fun witness => witness.headline == member headline && witness.derived).map
      (·.target.rendered)
  check (witnessOf `double_kept == some "∃ n h _x, n < 2")
    "the witness of double_kept does not keep its hypothesis input"
  check (witnessOf `double_kept_plain == some "∃ n h, SoftwareChallengeTests.Fixtures.KeptChallenge.double n < 2")
    "the witness of double_kept_plain drops the hypothesis a later input depends on"
  check (witnessOf `double_positive_one == some "0 < SoftwareChallengeTests.Fixtures.KeptChallenge.double 1")
    "a hypothesis that mentions no input was dropped from the witness"

run_cmd Elab.Command.liftCoreM do
  let member := fun (name : Name) => fixture (`StrayChallenge ++ name)
  let challenge ← challengeNamed (fixture `StrayChallenge)
  let some stray := challenge.headlines.find? (privateToUserName ·.target.constant.name == member `double_two)
    | throwError "a private theorem of the challenge was dropped"
  check (stray.target.constant.isPrivate && stray.target.written == "double_two" &&
      stray.target.enclosingNamespace == fixture `StrayChallenge) "a private theorem was misread"
  check (challenge.axioms.map (fun (name, place) => (name, place.line)) == #[(member `double_axiom, 19)])
    "an axiom of the challenge was misread"
  check (#[`Color.red, `Color.green].all fun name =>
      challenge.filled.any (·.1 == member name))
    s!"a declaration the challenge defines was not read as filled: {challenge.filled.map (·.1)}"
  check (#[(`Color, 21), (`triple, 25), (`Color._sizeOf_inst, 21), (`Color.rec, 0)].all fun (name, line) =>
      challenge.filled.any fun (found, place) => found == member name && place.line == line)
    "a declaration of the challenge was not placed at its own line, or a generated one at its owner's"
  let env := (← challengeEnv (← lakeOf #[] (some (fixture `StrayChallenge))) (fixture `StrayChallenge) .build).env
  check (challengeMisses env challenge).isEmpty "the census found a constant of the challenge the facts miss"
  let dropped := { challenge with filled := challenge.filled.filter (·.1 != member `Color.rec) }
  check (challengeMisses env dropped == #[member `Color.rec]) "the census missed a constant the facts drop"
  let refused ← refusal (requireChallengeCensus env dropped .build)
  check (refused.any fun message => contains message "SoftwareChallengeTests/Fixtures/StrayChallenge.lean:1:" &&
      contains message "Color.rec" && contains message "no edit to the package fixes this" &&
      contains message "then run `lake build`.")
    s!"the census did not refuse facts that miss a constant: {refused}"

run_cmd Elab.Command.liftCoreM do
  let challenge ← challengeNamed (fixture `AuxiliaryChallenge)
  let some first := challenge.headlines[0]? | throwError "first_is_zero was not read"
  check (first.target.auxiliaries.any (·.isPrivate) && first.target.auxiliaries.all fun auxiliary =>
      contains auxiliary.name.toString "first_is_zero._proof") "a private auxiliary of a statement was not read"
  check (first.target.signature == ": (⟨0, by omega⟩ : Fin 2).val = 0") "the signature of a statement was misread"

run_cmd Elab.Command.liftCoreM do
  let challenge := fixture `Challenge
  let lake ← lakeOf #[] (some challenge)
  let olean ← findOLean challenge
  let some library := (olean.parent.bind (·.parent)).bind (·.parent) | throwError "{olean} has no library"
  let dependency := (← IO.currentDir) / ".lake" / "build" / "readTests" / "shadow"
  if ← dependency.pathExists then IO.FS.removeDirAll dependency
  let shadow := dependency / "SoftwareChallengeTests" / "Fixtures" / "Challenge.olean"
  let saved ← searchPathRef.get
  try
    for file in ← (library / "SoftwareChallengeTests").walkDir do
      unless ← file.isDir do
        let some relative := file.toString.dropPrefix? library.toString | throwError "{file} is outside {library}"
        let copy : System.FilePath := dependency.toString ++ relative.toString
        IO.FS.createDirAll (copy.parent.getD dependency)
        IO.FS.writeBinFile copy (← IO.FS.readBinFile file)
    let other ← findOLean (fixture `CoreSpec)
    for extension in ["olean", "olean.server", "olean.private", "ir", "ir.sig"] do
      if ← (other.withExtension extension).pathExists then
        IO.FS.writeBinFile (shadow.withExtension extension) (← IO.FS.readBinFile (other.withExtension extension))
    searchPathRef.set (dependency :: saved)
    check ((← findOLean challenge) == shadow) "the dependency's challenge does not come first on the search path"
    let read ← readChallenge lake .lint
    check (read.holes.map (·.constant.name) == #[challenge ++ `double])
      s!"the reader read a dependency's {challenge}, not the root package's: holes {read.holes.map (·.constant.name)}"
  finally
    searchPathRef.set saved
    IO.FS.removeDirAll dependency

end

end SoftwareChallengeReadTests.Challenge

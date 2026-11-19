module

public import SoftwareChallenge.CoreCode.Report.LintMessages
public import SoftwareChallenge.CoreCode.Report.TestMessages
public import SoftwareChallenge.CoreCode.Rules.Follows
public import SoftwareChallenge.CoreCode.Match

public section

namespace SoftwareChallenge

open Lean

namespace Report

private def commandOf : Next → String
  | .build => "lake build"
  | .lint => "lake lint"
  | .test => "lake test"
  | .comparator => "lake comparator"
  | .replay => "lake script run software_challenge/replay"
  | .grade commit => s!"lake exe grade {commit}"

def item (message : Message) : String :=
  let head := s!"{message.place.file}:{message.place.line}: {message.what}, {message.why}. "
  match message.fix.splitOn "\n\n" with
  | fix :: block@(_ :: _) => head ++ s!"{fix}, then run `{commandOf message.next}`:\n\n{"\n\n".intercalate block}"
  | _ => head ++ s!"{message.fix}, then run `{commandOf message.next}`."

def listing (title : String) (items : Array String) : String :=
  "\n".intercalate (s!"{title}: {items.size}" :: items.toList.map fun item => "  " ++ item.replace "\n" "\n    ")

private def distinct (items : Array String) : Array String :=
  items.foldl (fun kept item => if kept.contains item then kept else kept.push item) #[]

structure Assumption where
  label : String
  checks : Nat
  unused : Bool
  deriving BEq, Repr, Inhabited

def Assumption.render (assumption : Assumption) : String :=
  let checks := s!"{assumption.checks} {if assumption.checks == 1 then "check" else "checks"}"
  s!"{assumption.label} ({checks}{if assumption.unused then ", unused by the proof" else ""})"

structure HeadlineLine where
  name : String
  assumptions : Array Assumption
  marks : Array String
  followsFrom : Array String
  deriving BEq, Repr, Inhabited

def HeadlineLine.render (line : HeadlineLine) : String :=
  let stated := if line.assumptions.isEmpty then line.name
    else s!"{line.name}  assumes {", ".intercalate (line.assumptions.map (·.render)).toList}"
  let marked := line.marks.foldl (fun shown mark => s!"{shown}  ({mark})") stated
  if line.followsFrom.isEmpty then marked else s!"{marked}  (follows from {", ".intercalate line.followsFrom.toList})"

private def sharedNamespace (names : Array Name) : Name :=
  let common := fun (shared : List Name) (name : Name) =>
    ((shared.zip name.getPrefix.components).takeWhile fun (left, right) => left == right).map (·.1)
  match names.toList with
  | [] => .anonymous
  | first :: rest => (rest.foldl common first.getPrefix.components).foldl (· ++ ·) .anonymous

private def shorten (shared : Name) (name : Name) : String :=
  if shared != .anonymous && shared.isPrefixOf name && name != shared then toString (name.replacePrefix shared .anonymous)
  else toString name

private def marker : Standing → Option String
  | .holds _ => none
  | .absent | .unsound _ => some "not yet proved"
  | .outside _ _ => some "outside Solution's imports"
  | .kind _ _ | .universes _ _ | .differs _ _ _ | .auxiliary _ _ => some "stated differently"

private def proved (facts : Facts) (target : TargetFact) : Bool :=
  (facts.solution.standingOf target).proved

private def assumptionsOf (facts : Facts) (headline : HeadlineFact) (short : Name → String) : Array Assumption :=
  let name := headline.target.constant.name
  let holds := proved facts headline.target
  let checksOf := fun (index : Nat) =>
    ((facts.solution.claimUses.find? fun use => use.headline == name && use.binder == index).map fun use =>
      (use.checks.filter (·.2 == .matched)).size).getD 0
  let groups := Lint.assumed headline
  groups.map fun group =>
    { label := if (groups.filter (·.claim == group.claim)).size > 1 then group.statement else short group.claim
      checks := ((group.binders[0]?).map checksOf).getD 0
      unused := Lint.unusedByProof facts.solution holds name group.binders }

private def markOf (facts : Facts) (kind : String) (targets : Array TargetFact) : Option String :=
  targets.findSome? fun target => (marker (facts.solution.standingOf target)).map fun shown => s!"{kind} {shown}"

def headlineLines (facts : Facts) : Array HeadlineLine :=
  let challenge := facts.challenge
  let short := shorten (sharedNamespace (challenge.headlines.map (·.target.constant.name)))
  let provedHeadlines := (challenge.headlines.filter (proved facts ·.target)).map (·.target.constant.name)
  let proofs := Lint.proofGraph facts.solution
  challenge.headlines.map fun headline =>
    let name := headline.target.constant.name
    let standing := facts.solution.standingOf headline.target
    let kills := (challenge.kills.filter (·.headline == name)).map (·.target)
    let witnesses := (challenge.witnesses.filter (·.headline == name)).map (·.target)
    { name := short name
      assumptions := assumptionsOf facts headline short
      marks := (marker standing).toArray ++ (markOf facts "kill" kills).toArray ++
        (markOf facts "witness" witnesses).toArray
      followsFrom := if standing.proved then (Lint.followsFrom proofs provedHeadlines name).map short
        else #[] }

def provedLine (facts : Facts) : String :=
  let counted := fun (targets : Array TargetFact) (label : String) =>
    if targets.isEmpty && label != "headlines" then none
    else some s!"{(targets.filter (proved facts)).size} of {targets.size} {label}"
  "Proved: " ++ ", ".intercalate ([counted (facts.challenge.headlines.map (·.target)) "headlines",
    counted (facts.challenge.kills.map (·.target)) "kills",
    counted (facts.challenge.witnesses.map (·.target)) "witnesses"].filterMap id)

def independentLine? (facts : Facts) : Option String :=
  let challenge := facts.challenge
  let independent := challenge.headlines.filter fun headline => challenge.kills.any fun kill =>
    kill.headline == headline.target.constant.name && proved facts kill.target &&
      headline.target.constant.type.independent challenge.isReplaceable (challenge.othersOf headline)
        kill.target.constant.type
  if independent.isEmpty then none
  else some s!"Independent: {independent.size} of {challenge.headlines.size} headlines"

def terminationLines (facts : Facts) : Array String :=
  let short := shorten (sharedNamespace (facts.challenge.headlines.map (·.target.constant.name)))
  facts.challenge.terminating.map fun termination =>
    s!"{short termination.definition} terminates via {short termination.headline}"

private def pendingOrder (facts : Facts) : Lint.Pending → Nat
  | .standing name _ => (Lint.hereOf facts name).line
  | _ => 0

private def verdict (errors pending : Array String) : Array String :=
  if !errors.isEmpty then
    #[s!"lake lint found {errors.size} {if errors.size == 1 then "error" else "errors"}, as listed under Errors \
      above, so the package does not pass `lake lint`. Fix each as it says, then run `lake lint`."]
  else if !pending.isEmpty then
    #[s!"lake lint found no errors, but {pending.size} {if pending.size == 1 then "item is" else "items are"} \
      pending, as listed under Pending above, so the solution is not complete. Do each as it says, then run \
      `lake lint`."]
  else #[]

def lint (facts : Facts) (errors : Array Lint.Error) (pending : Array Lint.Pending) : Array String :=
  let standings := (pending.filter (· matches .standing _ _)).qsort fun left right =>
    pendingOrder facts left < pendingOrder facts right
  let others := pending.filter (!· matches .standing _ _)
  let errorItems := distinct (errors.map fun error => item (error.message facts))
  let pendingItems := distinct ((standings ++ others).map fun found => item (found.message facts))
  (headlineLines facts).map (·.render) ++ #[provedLine facts] ++ (independentLine? facts).toArray ++
    terminationLines facts ++
    (if errorItems.isEmpty then #[] else #[listing "Errors" errorItems]) ++
    (if pendingItems.isEmpty then #[] else #[listing "Pending" pendingItems]) ++
    #["Edit: " ++ " ".intercalate (Lint.editableFiles facts).toList,
      "Owned: " ++ " ".intercalate (Lint.ownedList facts).toList] ++ verdict errorItems pendingItems

private def seconds (milliseconds : Nat) : String := s!"{milliseconds / 1000}.{milliseconds % 1000 / 100} s"

def test (challengeFile : String) (result : Test.Result) : Array String :=
  (result.timings.map fun outcome =>
    s!"{outcome.check.place.file}:{outcome.check.place.line} {outcome.check.claim}  {seconds outcome.elapsed}") ++
    distinct (result.failures.map fun failure => item (failure.message challengeFile))

end Report

end SoftwareChallenge

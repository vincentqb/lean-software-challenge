import SoftwareChallengeTests.Fixtures

namespace SoftwareChallengeTests

structure Context where
  lsc : System.FilePath
  root : System.FilePath

def Context.dir (context : Context) (name : String) : System.FilePath := context.root / name

abbrev Check := ExceptT String IO

def step (dir : System.FilePath) (args : Array String) (code : UInt32) (says : List String) : Check String := do
  let ran ← lakeIn dir args
  ExceptT.mk (pure (expect ran s!"`lake {" ".intercalate args.toList}` in {dir}" code says))
  return ran.output

def committed (dir : System.FilePath) (candidate : List Edit) : Check Unit := do
  if !(← (dir / ".git").pathExists) then discard <| gitIn dir #["init", "-q"]
  for args in [#["checkout", "-q", "-B", "base"], #["add", "-A"], #["commit", "-q", "--allow-empty", "-m", "base"]] do
    discard <| gitIn dir args
  discard <| gitIn dir #["checkout", "-q", "-B", "candidate"]
  for edit in candidate do edit.apply dir
  for args in [#["commit", "-q", "--allow-empty", "-am", "candidate"], #["checkout", "-q", "base"]] do
    discard <| gitIn dir args

def fixtureRun (context : Context) (fixture : Fixture) (name : String) : Check Unit := do
  let dir := context.dir name
  templateCopy context.lsc dir fixture.edits
  unless fixture.candidate.isEmpty do committed dir fixture.candidate
  discard <| step dir fixture.command fixture.code fixture.says

def comparatorIn (dir : System.FilePath) : Check String := do
  let mut ran ← lakeIn dir #["comparator"]
  for _ in [0:3] do
    unless ran.code != 0 && ran.output.contains "bwrap: Can't bind mount" do break
    IO.sleep 20000
    ran ← lakeIn dir #["comparator"]
  ExceptT.mk (pure (expect ran s!"`lake comparator` in {dir}" 0 ["Your solution is okay!"]))
  return ran.output

def lastLines (output : String) (count : Nat) : String :=
  "\n".intercalate (((output.splitOn "\n").filter (!·.isEmpty)).reverse.take count).reverse

def templateRun (context : Context) : Check String := do
  let dir := context.dir "template"
  templateCopy context.lsc dir []
  discard <| step dir #["build"] 0 []
  let linted ← step dir #["lint"] 0
    ["Proved: 6 of 6 headlines, 6 of 6 kills, 6 of 6 witnesses, 1 of 1 consistency theorems"]
  let tested ← step dir #["test"] 0 ["Tests: 2 of 2 passed"]
  let compared ← comparatorIn dir
  let program ← step dir #["exe", "constant_folding"] 0 ["5"]
  (Edit.replace "ConstantFolding/Expr.lean" "end ConstantFolding"
    "axiom closedLit : closed (.lit 0) = true\n\nend ConstantFolding").apply dir
  discard <| step dir statement 1 ["no @[consistent] theorem states"]
  return "\n".intercalate [lastLines linted 1, lastLines tested 3, lastLines compared 1, lastLines program 1]

def gradeRun (context : Context) : Check String := do
  let dir := context.dir "grade"
  templateCopy context.lsc dir []
  committed dir [.replace "ConstantFolding/Fold.lean" "end ConstantFolding"
    "theorem fold_lit (n : Nat) : fold (.lit n) = .lit n := fold_eq_self_of_normal _ rfl\n\nend ConstantFolding"]
  let graded ← step dir #["exe", "grade", "candidate"] 0 ["accepted: candidate"]
  return ((graded.splitOn "\n").find? (·.startsWith "accepted:")).getD ""

def coverageRun (context : Context) : Check Unit := do
  let dir := context.dir "coverage"
  templateCopy context.lsc dir coverage
  discard <| step dir #["build"] 0 []
  discard <| step dir #["lint"] 1 coverageSays

end SoftwareChallengeTests

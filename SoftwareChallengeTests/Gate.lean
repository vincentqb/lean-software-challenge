module

public import SoftwareChallenge.CoreCode.Grade
public import SoftwareChallenge.CoreCode.Format
public import SoftwareChallenge.Steps.Comparator
public import Lean.Data.Json

public section

namespace SoftwareChallengeTests.Gate

structure Context where
  lake : String
  lsc : System.FilePath
  root : System.FilePath
  jobs : Nat

structure Ran where
  shown : String
  dir : System.FilePath
  code : UInt32
  stdout : String
  stderr : String

def Ran.output (ran : Ran) : String :=
  ran.stdout ++ ran.stderr

def Ran.tail (ran : Ran) : String :=
  "\n".intercalate (((ran.output.splitOn "\n").reverse.take 150).reverse)

def unsetForChildren : Array (String × Option String) :=
  #[("GIT_DIR", none), ("GIT_WORK_TREE", none), ("GIT_INDEX_FILE", none), ("GIT_OBJECT_DIRECTORY", none),
    ("GIT_ALTERNATE_OBJECT_DIRECTORIES", none), ("GIT_CEILING_DIRECTORIES", none), ("LEAN_PATH", none)]

def runShown (shown : String) (dir : System.FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO Ran := do
  let out ← IO.Process.output { cmd, args, cwd := some dir, env := unsetForChildren ++ env }
  return { shown, dir, code := out.exitCode, stdout := out.stdout, stderr := out.stderr }

def Context.lakeIn (context : Context) (dir : System.FilePath) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO Ran :=
  runShown s!"lake {" ".intercalate args.toList}" dir context.lake args env

def gitIn (dir : System.FilePath) (args : Array String) : IO Ran :=
  runShown s!"git {" ".intercalate args.toList}" dir "git" (#["-c", "user.name=lsc-gate",
    "-c", "user.email=lsc-gate@localhost", "-c", "commit.gpgsign=false", "-c", "init.defaultBranch=base"] ++ args)

abbrev Trial := ExceptT String IO

def succeed (ran : Ran) (purpose fix next : String) : Trial Unit := do
  unless ran.code == 0 do
    throwThe String s!"`{ran.shown}` exited {ran.code} in {ran.dir}, so {purpose}. {fix}, then run `{next}`.\n\
      {ran.tail}"

inductive Result where
  | held
  | failed (message : String)
  | skipped (reason : String)

structure Outcome where
  check : String
  result : Result
  elapsed : Nat

def attempt {α : Type} (check next : String) (action : Trial α) : IO (Outcome × Option α) := do
  let start ← IO.monoMsNow
  let (result, value) ← try
      match ← action.run with
      | .ok value => pure (Result.held, some value)
      | .error message => pure (Result.failed message, none)
    catch error =>
      pure (Result.failed s!"the gate stopped on `{error}` before it could decide this, so the check is \
        undecided. Fix what it reports, then run `{next}`.", none)
  return ({ check, result, elapsed := (← IO.monoMsNow) - start }, value)

def check (name next : String) (action : Trial Unit) : IO Outcome :=
  Prod.fst <$> attempt name next action

def skipped (name reason : String) : Outcome :=
  { check := name, result := .skipped reason, elapsed := 0 }

def seconds (ms : Nat) : String :=
  s!"{ms / 1000}.{ms % 1000 / 100} s"

def Outcome.line (outcome : Outcome) : String :=
  match outcome.result with
  | .held => s!"  held     {outcome.check}  {seconds outcome.elapsed}"
  | .failed _ => s!"  FAILED   {outcome.check}  {seconds outcome.elapsed}"
  | .skipped reason => s!"  skipped  {outcome.check}: {reason}"

def Outcome.failure? (outcome : Outcome) : Option String :=
  match outcome.result with
  | .failed message => some s!"FAILED {outcome.check}: {message}"
  | _ => none

def Outcome.held (outcome : Outcome) : Bool :=
  match outcome.result with
  | .held => true
  | _ => false

def report (title : String) (outcomes : Array Outcome) (elapsed : Nat) : String :=
  let failures := outcomes.filterMap (·.failure?)
  let held := (outcomes.filter (·.held)).size
  let skippedCount := outcomes.size - held - failures.size
  "\n".intercalate ([title] ++ (outcomes.map (·.line)).toList ++
    [s!"{held} of {outcomes.size} checks held, {failures.size} failed and {skippedCount} skipped, in \
      {seconds elapsed}"] ++ failures.toList)

abbrev Edit := System.FilePath × (String → Option String)

def replacing (old new : String) (text : String) : Option String :=
  if (text.splitOn old).length == 2 then some (text.replace old new) else none

def appending (addition : String) (text : String) : Option String :=
  some (text ++ addition)

def applyEdits (dir : System.FilePath) (source next : String) (edits : List Edit) : Trial Unit := do
  for (file, edit) in edits do
    let path := dir / file
    if let some parent := path.parent then IO.FS.createDirAll parent
    let text ← if ← path.pathExists then IO.FS.readFile path else pure ""
    let some edited := edit text | throwThe String s!"{file}: the text that an edit in {source} replaces does not \
      occur exactly once in {path}, so the gate cannot make that edit. Change that `replacing` text in {source} \
      to the file's current text, then run `{next}`."
    IO.FS.writeFile path edited

partial def copyTree (source destination : System.FilePath) (skip : String → Bool) : IO Unit := do
  if ← source.isDir then
    IO.FS.createDirAll destination
    for entry in ← source.readDir do
      unless skip entry.fileName do copyTree entry.path (destination / entry.fileName) skip
  else
    IO.FS.writeBinFile destination (← IO.FS.readBinFile source)

def fresh (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir

def exclusively {α : Type} (file : System.FilePath) (action : IO α) : IO α := do
  if let some parent := file.parent then IO.FS.createDirAll parent
  let handle ← IO.FS.Handle.mk file .append
  handle.lock
  try action finally handle.unlock

def concurrently {α : Type} (jobs : Nat) (actions : Array (IO α)) : IO (Array α) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (#[] : Array (Nat × α))
  let worker : IO Unit := do
    repeat
      let index ← next.modifyGet fun index => (index, index + 1)
      let some action := actions[index]? | break
      let value ← action
      results.modify (·.push (index, value))
  let workers ← (List.range (min actions.size (max 1 jobs))).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for task in workers do IO.ofExcept task.get
  return ((← results.get).qsort (·.1 < ·.1)).map (·.2)

end SoftwareChallengeTests.Gate

namespace SoftwareChallengeTests.Gate.TemplateRun

open SoftwareChallenge

def next : String := "lake build templateRun"

def source : String := "SoftwareChallengeTests/Gate.lean"

def challengeFile : System.FilePath := "Challenge.lean"

def solutionFile : System.FilePath := "ConstantFolding" / "Solution.lean"

def checkCount : Nat := 2

def droppedKill : List Edit := [
  (challengeFile, replacing "@[kills fold_normalizes] theorem fold_normalizes_rejects_identity : \
    ¬ ∀ e, normal (id e) = true := by\n  sorry\n\n" "")]

structure Recorded where
  lock : String
  config : String

def overridesFor (lsc : System.FilePath) : String :=
  (Lean.Json.mkObj [("version", "1.3.0"), ("packages", Lean.Json.arr #[Lean.Json.mkObj [("type", "path"),
    ("scope", ""), ("name", "software_challenge"), ("manifestFile", "lake-manifest.json"), ("inherited", false),
    ("dir", lsc.toString), ("copy", false), ("configFile", "lakefile.lean")]])]).pretty

def requireLocally (lsc dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (dir / ".lake")
  IO.FS.writeFile (dir / ".lake" / "package-overrides.json") (overridesFor lsc)

def prepare (context : Context) (dir : System.FilePath) (next : String) : Trial Recorded := do
  if ← dir.pathExists then IO.FS.removeDirAll dir
  copyTree (context.lsc / "Examples" / "ConstantFolding") dir fun name =>
    name == ".lake" || name == "comparator.json" || name == "owned.lock"
  requireLocally context.lsc dir
  let built ← (exclusively (context.root / "template-build.lock") (context.lakeIn dir #["build"]) : IO Ran)
  succeed built "a copy of the template without owned.lock and comparator.json does not build"
    "Fix what the output below reports, in the library or in Examples/ConstantFolding" next
  for file in ["owned.lock", "comparator.json"] do
    unless ← (dir / file).pathExists do
      throwThe String s!"{file}: `lake build` exited 0 in {dir} but did not write it, so the statement step no longer \
        records what grade and replay read. Make the statement step write {file} again, then run `{next}`.\n\
        {built.tail}"
  let committed ← IO.FS.readFile (context.lsc / "Examples" / "ConstantFolding" / "owned.lock")
  unless (← IO.FS.readFile (dir / "owned.lock")) == committed do
    throwThe String s!"Examples/ConstantFolding/owned.lock: it differs from the owned.lock that `lake build` records \
      for an unchanged copy of the template, so the template's lock is stale. Run `rm owned.lock && lake build` in \
      a copy of Examples/ConstantFolding whose .lake/package-overrides.json points software_challenge at this \
      checkout, copy its owned.lock into Examples/ConstantFolding, then run `{next}`."
  for args in [#["init", "-q"], #["add", "-A"], #["commit", "-q", "-m", "base"]] do
    succeed (← gitIn dir args) "the gate cannot commit the template copy that later checks reset to"
      "Fix what git reports" next
  return { lock := ← IO.FS.readFile (dir / "owned.lock"), config := ← IO.FS.readFile (dir / "comparator.json") }

def reset (dir : System.FilePath) : Trial Unit := do
  for args in [#["checkout", "-q", "--", "."], #["clean", "-fdq"]] do
    succeed (← gitIn dir args) "the gate cannot return the template copy to its committed state"
      "Fix what git reports" next

def outOfDate (ran : Ran) : String :=
  let stale := (ran.output.splitOn "\n").filterMap fun line =>
    if line.startsWith "✖" then (line.splitOn "Building ").getLast? else none
  if stale.isEmpty then "a target" else ", ".intercalate stale

def idle (context : Context) (dir : System.FilePath) (recorded : Recorded) : Trial Unit := do
  let ran ← context.lakeIn dir #["build", "--no-build"]
  unless ran.code == 0 do
    let again ← context.lakeIn dir #["build"]
    let settled ← context.lakeIn dir #["build", "--no-build"]
    let after := if again.code == 0 && settled.code == 0 then "; one more build settles it, and the build after \
      that is idle" else "; one more build does not settle it either"
    throwThe String s!"`lake build --no-build` exited {ran.code} in {dir} right after the build that recorded \
      owned.lock, so a consumer who re-locks with `rm owned.lock && lake build` reruns {outOfDate ran} on the next \
      build{after}. The statement step traces owned.lock, which its own first run writes: make record in \
      lakefile.lean save the step's trace with the lock it records, then run `{next}`.\n{ran.tail}"
  for (file, before) in [("owned.lock", recorded.lock), ("comparator.json", recorded.config)] do
    unless (← IO.FS.readFile (dir / file)) == before do
      throwThe String s!"{file}: the second `lake build` in {dir} rewrote it with other bytes, so the file the \
        statement step records is not stable across builds. Make the statement step render {file} from its \
        inputs alone, then run `{next}`."

def reportOf (dir : System.FilePath) : IO (List String) := do
  let file := dir / ".lake" / "build" / "softwareChallenge" / "lint.out"
  unless ← file.pathExists do return []
  return ((← IO.FS.readFile file).splitOn "\n").filter (!·.isEmpty)

def lintAccepts (context : Context) (dir : System.FilePath) : Trial (List String) := do
  let ran ← context.lakeIn dir #["lint"]
  unless ran.code == 0 do
    throwThe String s!"`lake lint` exited {ran.code} in {dir}, expected 0, so an unchanged copy of the template does \
      not pass lint. Fix what the output below reports, in the library or in Examples/ConstantFolding, then run \
      `{next}`.\n{ran.tail}"
  reportOf dir

def checksTimed (ran : Ran) : Nat :=
  ((ran.output.splitOn "\n").filter fun line =>
    line.startsWith "ConstantFolding/WorldCode.lean:" && line.contains " ConstantFolding.AddAgrees ").length

def testRunsChecks (context : Context) (dir : System.FilePath) : Trial Unit := do
  let ran ← context.lakeIn dir #["test"]
  unless ran.code == 0 && checksTimed ran == checkCount do
    throwThe String s!"`lake test` exited {ran.code} in {dir} and timed {checksTimed ran} Checks of \
      ConstantFolding/WorldCode.lean, expected exit 0 and {checkCount} Checks, so the template's Checks, which call \
      nativeAdd from its extern_lib, do not all run and pass. Fix what the output below reports, such as \
      test_challenge in lakefile.lean no longer passing each extern_lib's dynlib to the Checks with \
      `--load-dynlib`; if the template's Checks or the lines that time them changed on purpose, change checkCount \
      or checksTimed in {source}. Then run `{next}`.\n{ran.tail}"

def ownerDropsKill (context : Context) (dir : System.FilePath) : Trial Unit := do
  reset dir
  applyEdits dir source next droppedKill
  IO.FS.removeFile (dir / "owned.lock")
  let ran ← context.lakeIn dir #["build"]
  reset dir
  unless ran.code == 1 && ran.output.contains "@[kills fold_normalizes]" && ran.output.contains "?wrong_fold" do
    throwThe String s!"`lake build` exited {ran.code} in {dir} after the owner dropped fold_normalizes' kill from \
      Challenge.lean, expected 1 with a kill to write, `@[kills fold_normalizes] …` with `?wrong_fold` in it, so \
      an owner is not told how to show that fold_normalizes rejects a wrong fold. Restore the statement check's \
      missing-kill error and its template, then run `{next}`.\n{ran.tail}"

structure Presentation where
  name : String
  moves : List (System.FilePath × System.FilePath) := []
  edits : List Edit

def coreCodeFile : System.FilePath := "ConstantFolding" / "CoreCode.lean"

def worldCodeFile : System.FilePath := "ConstantFolding" / "WorldCode.lean"

def presentations : List Presentation := [
  { name := "a world claim restated under ∀", edits := [
      (challengeFile, replacing "theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :"
        "theorem output_correct (agrees : ∀ _ : Unit, AddAgrees nativeAdd) (e : Expr) :"),
      (challengeFile, replacing "¬ (AddAgrees Nat.add → ∀ e : Expr,"
        "¬ ((∀ _ : Unit, AddAgrees Nat.add) → ∀ e : Expr,"),
      (solutionFile, replacing "theorem output_correct (agrees : AddAgrees nativeAdd) (e : Expr) :"
        "theorem output_correct (agrees : ∀ _ : Unit, AddAgrees nativeAdd) (e : Expr) :"),
      (solutionFile, replacing "evalNative_eq agrees," "evalNative_eq (agrees ()),"),
      (solutionFile, replacing "¬ (AddAgrees Nat.add → ∀ e : Expr," "¬ ((∀ _ : Unit, AddAgrees Nat.add) → ∀ e : Expr,"),
      (solutionFile, replacing "(h (fun _ _ => rfl) (.lit 0))" "(h (fun _ _ _ => rfl) (.lit 0))")] },
  { name := "roots narrowed, globs kept", edits := [
      ("lakefile.lean", replacing "roots := #[`ConstantFolding.Solution]" "roots := #[`ConstantFolding.CoreCode]")] },
  { name := "CoreCode moved to a submodule", moves := [(coreCodeFile, "ConstantFolding" / "CoreCode" / "Fold.lean")],
    edits := [(worldCodeFile, replacing "public import ConstantFolding.CoreCode\n"
      "public import ConstantFolding.CoreCode.Fold\n")] },
  { name := "a headline and its kill declared outside the namespace", edits := [
      (challengeFile, replacing "theorem fold_keeps_literal (n m : Nat) (h : fold (.lit n) = .lit m) : m = n := by\n  \
        sorry\n\n" ""),
      (challengeFile, replacing "@[kills fold_keeps_literal] theorem fold_keeps_literal_rejects_zero :\n    \
        ¬ ∀ (n m : Nat), (fun (_ : Expr) => Expr.lit 0) (.lit n) = .lit m → m = n := by\n  sorry\n\n" ""),
      (challengeFile, replacing "end ConstantFolding\n" "end ConstantFolding\n\n\
        theorem ConstantFolding.fold_keeps_literal (n m : Nat)\n    \
        (h : ConstantFolding.fold (.lit n) = .lit m) : m = n := by\n  sorry\n\n\
        @[kills ConstantFolding.fold_keeps_literal] theorem ConstantFolding.fold_keeps_literal_rejects_zero :\n    \
        ¬ ∀ (n m : Nat), (fun (_ : ConstantFolding.Expr) => ConstantFolding.Expr.lit 0) (.lit n) = .lit m → m = n := \
        by\n  sorry\n"),
      (solutionFile, replacing "theorem fold_normalizes (e : Expr) :"
        "theorem _root_.ConstantFolding.fold_normalizes (e : Expr) :")] },
  { name := "a kill marked by `attribute` afterwards", edits := [
      (challengeFile, replacing "@[kills fold_keeps_literal] theorem fold_keeps_literal_rejects_zero :\n    \
        ¬ ∀ (n m : Nat), (fun (_ : Expr) => Expr.lit 0) (.lit n) = .lit m → m = n := by\n  sorry\n" "theorem \
        fold_keeps_literal_rejects_zero :\n    ¬ ∀ (n m : Nat), (fun (_ : Expr) => Expr.lit 0) (.lit n) = .lit m → \
        m = n := by\n  sorry\n\nattribute [kills fold_keeps_literal] fold_keeps_literal_rejects_zero\n")] }]

def presentationDir (context : Context) (presentation : Presentation) : System.FilePath :=
  context.root / "presentation" / (presentation.name.map fun char => if char.isAlphanum then char else '-')

def stage (context : Context) (warm : System.FilePath) (presentation : Presentation) : Trial Unit := do
  let dir := presentationDir context presentation
  if ← dir.pathExists then IO.FS.removeDirAll dir
  copyTree (context.lsc / "Examples" / "ConstantFolding") dir fun name =>
    name == ".lake" || name == "comparator.json" || name == "owned.lock"
  copyTree (warm / ".lake") (dir / ".lake") fun _ => false
  for (old, new) in presentation.moves do
    if let some parent := (dir / new).parent then IO.FS.createDirAll parent
    IO.FS.rename (dir / old) (dir / new)
  applyEdits dir source next presentation.edits

def invariant (lines : List String) : Array String :=
  (lines.filter fun line => !line.startsWith "Edit:" && !line.startsWith "Owned:").toArray.qsort (· < ·)

def targetsOf (config : Config) : Array String × Array String :=
  ((config.theorems.map toString).qsort (· < ·), (config.definitions.map toString).qsort (· < ·))

def presents (context : Context) (reference : Task (Option (List String))) (config : Config)
    (presentation : Presentation) : Trial Unit := do
  let dir := presentationDir context presentation
  let changed := s!"the template with {presentation.name}, which changes only how the challenge or the solution is \
    written,"
  let fix := s!"Make the rule that depends on that presentation depend on meaning; if the template changed, change \
    the edits of \"{presentation.name}\" in presentations in {source}"
  succeed (← context.lakeIn dir #["build"]) s!"{changed} does not build" fix next
  let linted ← context.lakeIn dir #["lint"]
  let reported ← reportOf dir
  let some expected ← IO.wait reference | throwThe String s!"`lake lint` fails on the unchanged template, as the \
    check that lint accepts it reports, so the gate has no standings to compare {changed} with. Fix that failure \
    first, then run `{next}`."
  unless linted.code == 0 && invariant reported == invariant expected do
    throwThe String s!"`lake lint` exited {linted.code} in {dir} and reported {reported}, expected 0 and the \
      standings {invariant expected} of the unchanged template, so lint judges {changed} as a change of meaning. \
      {fix}, then run `{next}`.\n{linted.tail}"
  let tested ← context.lakeIn dir #["test"]
  unless tested.code == 0 && checksTimed tested == checkCount do
    throwThe String s!"`lake test` exited {tested.code} in {dir} and timed {checksTimed tested} Checks, expected 0 \
      and {checkCount}, so test judges {changed} as a change of meaning. {fix}, then run `{next}`.\n{tested.tail}"
  let configFile := dir / "comparator.json"
  let some written := Config.parse (← IO.FS.readFile configFile) | throwThe String s!"{configFile}:1: Config.parse \
    cannot read it, so grade could not read the statement of {changed}. Make the statement step write it with \
    Config.render, then run `{next}`."
  unless targetsOf written == targetsOf config do
    throwThe String s!"{dir / "comparator.json"}:1: it lists the theorems and holes {targetsOf written}, but the \
      unchanged template's lists {targetsOf config}, so the statement step names the targets of {changed} \
      differently. {fix}, then run `{next}`."

def builtinLinted : Presentation :=
  { name := "builtinLint := true and fold_idempotent unproved", edits := [
      ("lakefile.lean", replacing "package «constant_folding» where\n"
        "package «constant_folding» where\n  builtinLint := true\n"),
      (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
        fold_eq_self_of_normal (fold e) (normal_fold e)\n\n" "")] }

def unusedHypothesis : List Edit :=
  [(solutionFile, appending "\ntheorem ConstantFolding.self_eq (n : Nat) (h : n = n) : n = n := rfl\n")]

def builtinLintKeepsCodes (context : Context) : Trial Unit := do
  let dir := presentationDir context builtinLinted
  succeed (← context.lakeIn dir #["build"]) s!"the template with {builtinLinted.name} does not build"
    s!"Fix what the output below reports, or the edits of builtinLinted in {source}" next
  let pending ← context.lakeIn dir #["lint"]
  unless pending.code == 2 do
    throwThe String s!"`lake lint` exited {pending.code} in {dir}, expected 2, so a package that sets `builtinLint := \
      true` and leaves only fold_idempotent unproved is not reported as pending. Make the lint driver report each \
      finding of Lake's builtin lint printed below and exit 2 when only pending items remain, then run `{next}`.\n\
      {pending.tail}"
  applyEdits dir source next unusedHypothesis
  let warned ← context.lakeIn dir #["lint"]
  unless warned.code == 1 && warned.output.contains "Lean's linter linter.unusedVariables" do
    throwThe String s!"`lake lint` exited {warned.code} in {dir}, expected 1 with lint's report of the unused \
      hypothesis h of ConstantFolding.self_eq in {solutionFile}, so a package that sets `builtinLint := true` passes \
      a warning of Lean's linters. Make the lint step refuse each warning of Lean's linters, then run `{next}`.\n\
      {warned.tail}"

def run (context : Context) : IO (Array Outcome) := do
  let dir := context.root / "template"
  let (setup, recorded?) ← attempt "build writes owned.lock and comparator.json in a fresh copy" next
    (prepare context dir next)
  let some recorded := recorded? | return #[setup]
  let staged ← presentations.toArray.mapM fun presentation =>
    return (presentation, ← attempt s!"{presentation.name}: the copy is staged" next (stage context dir presentation))
  let (builtinStaging, builtinStaged?) ← attempt s!"{builtinLinted.name}: the copy is staged" next
    (stage context dir builtinLinted)
  let idled ← check "a second build is idle and rewrites neither file" next (idle context dir recorded)
  let linted ← IO.asTask (prio := .dedicated) (attempt "lint accepts the template" next (lintAccepts context dir))
  let reference := linted.map fun result => match result with
    | .ok (_, report?) => report?
    | .error _ => none
  let presented ← IO.asTask (prio := .dedicated) <| concurrently context.jobs <| staged.map
    fun (presentation, (staging, ready?)) =>
      let name := s!"{presentation.name}: build, lint and test judge it as the unchanged template"
      match ready?, Config.parse recorded.config with
      | some _, some config => check name next (presents context reference config presentation)
      | none, _ => pure staging
      | _, none => pure (skipped name "the template's comparator.json is unreadable")
  let builtin ← IO.asTask (prio := .dedicated) <| if builtinStaged?.isSome then
      check s!"{builtinLinted.name}: lint exits 2, and 1 once Lean's linters warn" next (builtinLintKeepsCodes context)
    else pure builtinStaging
  let mut outcomes := #[setup, idled, (← IO.ofExcept linted.get).1]
  for (name, action) in [
      (s!"test runs and passes the template's {checkCount} Checks, which call nativeAdd from its extern_lib",
        testRunsChecks context dir),
      ("an owner who drops fold_normalizes' kill fails the build with the kill to write",
        ownerDropsKill context dir)] do
    outcomes := outcomes.push (← check name next action)
  return outcomes ++ (← IO.ofExcept presented.get) ++ #[← IO.ofExcept builtin.get]

end SoftwareChallengeTests.Gate.TemplateRun

namespace SoftwareChallengeTests.Gate.ComparatorRun

open Lean SoftwareChallenge

def next : String := "lake build comparatorRun"

def source : String := "SoftwareChallengeTests/Gate.lean"

structure Case where
  name : String
  solution : Name := `Cases.Solution
  theorems : Array Name := #[]
  definitions : Array Name := #[]
  verdict : Verdict
  rejection : Option Comparator.Rejection := none
  says : Option String := none

def expectations : List Case := [
  { name := "renamed binders", theorems := #[`Cases.renamed], verdict := .accept },
  { name := "an implicit binder", theorems := #[`Cases.implicit], verdict := .accept },
  { name := "no_index in the challenge", theorems := #[`Cases.noIndexLeft], verdict := .accept },
  { name := "no_index in the solution", theorems := #[`Cases.noIndexRight], verdict := .accept },
  { name := "let in the challenge, have in the solution", theorems := #[`Cases.letHave], verdict := .accept },
  { name := "a hole implemented by a def", definitions := #[`Cases.implemented], verdict := .accept },
  { name := "a statement that differs", theorems := #[`Cases.differs], verdict := .refuse,
    rejection := some .statement },
  { name := "a theorem the solution lacks", theorems := #[`Cases.absent], verdict := .refuse,
    rejection := some (.missing "Cases.absent") },
  { name := "a theorem outside the solution's imports", theorems := #[`Cases.outside], verdict := .refuse,
    rejection := some (.missing "Cases.outside") },
  { name := "a def in place of a theorem", theorems := #[`Cases.kind], verdict := .refuse, rejection := some .kind },
  { name := "renamed universe parameters", theorems := #[`Cases.universes], verdict := .refuse,
    rejection := some .statement },
  { name := "a custom axiom", theorems := #[`Cases.axiomUsed], verdict := .refuse, rejection := some .axiomUsed },
  { name := "a partial def in place of a hole", definitions := #[`Cases.partialHole], verdict := .refuse,
    rejection := some .notDefinition },
  { name := "a hole of another type", definitions := #[`Cases.mistyped], verdict := .refuse,
    rejection := some .differs },
  { name := "a proof forged with debug.skipKernelTC", solution := `Cases.Forged, theorems := #[`Cases.forgery],
    verdict := .refuse, rejection := some .kernel },
  { name := "a solution that does not compile, which grade's build stage refuses first", solution := `Cases.Broken,
    theorems := #[`Cases.compiles], verdict := .cannotJudge, says := some "Cases/Broken.lean" }]

def permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def configOf (case : Case) : Config :=
  { challenge := `Challenge, solution := case.solution, theorems := case.theorems, definitions := case.definitions,
    axioms := permitted }

def hiddenCase (hidden : System.FilePath) : Case :=
  { name := "a dependency under /tmp, which the sandbox hides", solution := `Solution,
    theorems := #[`hiddenValue], verdict := .cannotJudge, says := some hidden.toString }

def verdictWord : Verdict → String
  | .accept => "accept"
  | .refuse => "refuse"
  | .cannotJudge => "cannot judge"

def rejectionWord : Comparator.Rejection → String
  | .kernel => "kernel"
  | .statement => "statement"
  | .kind => "kind"
  | .absent => "absent"
  | .unexported => "unexported"
  | .differs => "differs"
  | .notDefinition => "notDefinition"
  | .notTheorem => "notTheorem"
  | .axiomUsed => "axiomUsed"
  | .missing name => s!"missing {name}"

def shown (verdict : Verdict) : Option Comparator.Rejection → String
  | some rejection => s!"{verdictWord verdict} ({rejectionWord rejection})"
  | none => verdictWord verdict

def Case.expected (case : Case) : String :=
  shown case.verdict case.rejection ++ ((case.says.map (s!", naming {·}")).getD "")

def judged (context : Context) (project configFile : System.FilePath) (case : Case) : Trial Unit := do
  let out ← Steps.Comparator.run context.lake project configFile (configOf case)
  let text := out.stdout ++ "\n" ++ out.stderr
  let verdict := Comparator.classify out.exitCode text
  let rejection := Comparator.rejection? out.exitCode text
  let named := (case.says.map fun says => text.contains says).getD true
  unless verdict == case.verdict && (case.rejection.isNone || rejection == case.rejection) && named do
    let got := shown verdict rejection ++ (if named then "" else ", naming none of that")
    throwThe String s!"`lake comparator --config {configFile}` exited {out.exitCode} in {project} for \
      {", ".intercalate ((case.theorems ++ case.definitions).toList.map toString)}, which Comparator.classify in \
      SoftwareChallenge/CoreCode/Grade.lean reads as {got}, expected {case.expected}, so grade would decide this \
      case otherwise than the gate states. If the case's files in SoftwareChallengeTests/Comparator changed, restore \
      them; if Lake's text changed, update Comparator.rejections there; if the comparator's verdict changed on \
      purpose, change this case in `expectations` in {source}. Then run `{next}`.\n{out.stdout}{out.stderr}"

def hiddenPackage : List (System.FilePath × String) := [
  ("lakefile.lean", "import Lake\nopen Lake DSL\n\npackage «hidden»\n\nlean_lib «Hidden»\n"),
  ("Hidden.lean", "module\n\npublic section\n\ndef Hidden.value : Nat := 1\n")]

def consumerPackage (hidden : System.FilePath) : List (System.FilePath × String) := [
  ("lakefile.lean", s!"import Lake\nopen Lake DSL\n\npackage «hidden_consumer»\n\nrequire hidden from \
    \"{hidden}\"\n\nlean_lib «Challenge» where\n  leanOptions := #[⟨`warn.sorry, false⟩]\n\n\
    @[default_target]\nlean_lib «Solution»\n"),
  ("Challenge.lean", "module\n\npublic import Hidden\n\npublic section\n\n\
    theorem hiddenValue : Hidden.value = Hidden.value := by\n  sorry\n"),
  ("Solution.lean", "module\n\npublic import Hidden\n\npublic section\n\n\
    theorem hiddenValue : Hidden.value = Hidden.value := rfl\n")]

def writeFiles (dir : System.FilePath) (toolchain : String) (files : List (System.FilePath × String)) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "lean-toolchain") toolchain
  for (file, text) in files do IO.FS.writeFile (dir / file) text

def prepareHidden (context : Context) (hidden consumer : System.FilePath) : Trial Unit := do
  let toolchain ← IO.FS.readFile (context.lsc / "lean-toolchain")
  writeFiles hidden toolchain hiddenPackage
  writeFiles consumer toolchain (consumerPackage hidden)
  succeed (← context.lakeIn consumer #["build", "Challenge", "Solution"])
    "a package that requires a dependency under /tmp does not build outside the sandbox, so its comparator run \
      would not show what the sandbox hides" s!"Fix what the output below reports in hiddenPackage or \
      consumerPackage in {source}" next

def dependencyDirs (project : System.FilePath) : Trial (Array String) := do
  let text ← IO.FS.readFile (project / "lake-manifest.json")
  let dirs ← match Json.parse text >>= (·.getObjValAs? (Array Json) "packages") >>=
      (·.mapM (·.getObjValAs? String "dir")) with
    | .ok dirs => pure dirs
    | .error problem => throwThe String s!"{project / "lake-manifest.json"}: it lists no package directories the \
        gate can read ({problem}), so the gate cannot tell which dependencies the sandbox hides. Run `lake build` \
        in {project} to rewrite it, then run `{next}`."
  dirs.mapM fun dir => do
    let path : System.FilePath := if dir.startsWith "/" then dir else project / dir
    return (← IO.FS.realPath path).toString

def coversOnlyHidden (project consumer hidden : System.FilePath) : Trial Unit := do
  let flagged := (← dependencyDirs project).filter Sandbox.covers
  let expected := #[(← IO.FS.realPath hidden).toString]
  let found := (← dependencyDirs consumer).filter Sandbox.covers
  unless flagged.isEmpty && found == expected do
    throwThe String s!"Sandbox.covers in SoftwareChallenge/CoreCode/Grade.lean flags {flagged} among the cases' \
      dependencies and {found} among the consumer's, expected none and {expected}, so grade's dependency stage \
      would not name the dependency the sandbox hides. Make Sandbox.coveredRoots list the directories that `lake \
      comparator` masks, then run `{next}`."

def casesModules : Array String := #["Cases.Solution", "Cases.Elsewhere", "Cases.Forged"]

def standingsAgree (context : Context) (project : System.FilePath) : Trial Unit := do
  let runner := context.lsc / "SoftwareChallengeTests" / "Gate" / "Read.lean"
  let ran ← context.lakeIn context.lsc (#["env", "lean", "--run", runner.toString, "comparator", project.toString] ++
    casesModules)
  succeed ran "the reader cannot read the facts of the comparator cases, so the standing rule has nothing to judge"
    "Fix what the output below reports in SoftwareChallenge/Read or SoftwareChallengeTests/Comparator" next
  let judged := (ran.stdout.splitOn "\n").filterMap fun line => match line.splitOn " " with
    | name :: verdict@(_ :: _) => some (name, " ".intercalate verdict)
    | _ => none
  let wrong := (expectations.filter (·.solution == `Cases.Solution)).filterMap fun case =>
    let names := (case.theorems ++ case.definitions).toList.map toString
    let found := names.map fun name => ((judged.find? (·.1 == name)).map (·.2)).getD "no verdict"
    if found.all (· == verdictWord case.verdict) then none else some s!"{case.name}: {found}, expected {case.expected}"
  unless wrong.isEmpty do
    throwThe String s!"SoftwareChallengeTests/Gate/Read.lean:1: the standing rule judges the reader's facts of \
      {project} otherwise than `lake comparator` does: {"; ".intercalate wrong}, so lint's standings do not predict \
      the comparator. Make Shape.ofExpr and the standing rule follow ExprSimilar, then run `{next}`."

def run (context : Context) : IO (Array Outcome) := do
  let dir := context.root / "comparator"
  fresh dir
  let project := dir / "cases"
  let consumer := dir / "consumer"
  let (setup, built?) ← attempt "the cases package builds, but for the case that must not compile" next do
    copyTree (context.lsc / "SoftwareChallengeTests" / "Comparator") project (· == ".lake")
    succeed (← context.lakeIn project #["build", "Challenge", "Cases"])
      "the comparator cases do not build outside the sandbox, so their verdicts would say nothing"
      "Fix what the output below reports in SoftwareChallengeTests/Comparator" next
  if built?.isNone then return #[setup]
  let hidden : System.FilePath := "/tmp" / s!"lsc-gate-{← IO.Process.getPID}-{← IO.monoNanosNow}" / "hidden"
  try
    let (hiddenSetup, ready?) ← attempt "a consumer of a dependency under /tmp builds outside the sandbox" next
      (prepareHidden context hidden consumer)
    let configs := dir / "configs"
    IO.FS.createDirAll configs
    let judgements := (expectations.toArray.mapIdx fun index case =>
      check s!"{case.name}: {shown case.verdict case.rejection}" next
        (judged context project (configs / s!"{index}.json") case)) ++
      (if ready?.isSome then
        #[check s!"{(hiddenCase hidden).name}: {shown .cannotJudge none}" next
          (judged context consumer (configs / "hidden.json") (hiddenCase hidden))]
      else #[])
    let outcomes ← concurrently context.jobs judgements
    let sandbox ← if ready?.isSome then
        check "Sandbox.covers flags only the dependency under /tmp" next (coversOnlyHidden project consumer hidden)
      else pure (skipped "Sandbox.covers flags only the dependency under /tmp" "its consumer did not build")
    let agrees ← check "the standing rule gives these verdicts on the reader's facts, but for the forgery and the \
      solution that does not build, which have no facts that show why" next (standingsAgree context project)
    return #[setup, hiddenSetup] ++ outcomes ++ #[sandbox, agrees]
  finally
    if let some scratch := hidden.parent then
      if ← scratch.pathExists then IO.FS.removeDirAll scratch

end SoftwareChallengeTests.Gate.ComparatorRun

namespace SoftwareChallengeTests.Gate.GradeRun

def next : String := "lake build gradeRun"

def source : String := "SoftwareChallengeTests/Gate.lean"

def challengeFile : System.FilePath := "Challenge.lean"

def coreCodeFile : System.FilePath := "ConstantFolding" / "CoreCode.lean"

def solutionFile : System.FilePath := "ConstantFolding" / "Solution.lean"

structure Candidate where
  name : String
  edits : List Edit
  relocks : Bool := false

def weakened : List Edit := [
  (challengeFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :="
    "theorem fold_idempotent (e : Expr) (_ : normal e = true) : fold (fold e) = fold e :="),
  (challengeFile, replacing "    ¬ ∀ e : Expr, (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"
    "    ¬ ∀ e : Expr, normal e = true → (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"),
  (solutionFile, replacing "theorem fold_idempotent (e : Expr) : fold (fold e) = fold e :="
    "theorem fold_idempotent (e : Expr) (_ : normal e = true) : fold (fold e) = fold e :="),
  (solutionFile, replacing "    ¬ ∀ e : Expr, (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"
    "    ¬ ∀ e : Expr, normal e = true → (fun e => Expr.lit (eval (fun _ => 0) e + 1)) ((fun e"),
  (solutionFile, replacing "  have := h (.lit 0)\n" "  have := h (.lit 0) rfl\n")]

def forged : String :=
  "set_option debug.skipKernelTC true in\nrun_meta Lean.addDecl (.thmDecl { name := `ConstantFolding.fold_forged, \
    levelParams := [], value := Lean.mkConst ``True.intro, type := .forallE `e (Lean.mkConst ``Expr) \
    (Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.one]) (Lean.mkConst ``Expr) (Lean.mkApp (Lean.mkConst ``fold) \
    (.bvar 0)) (.bvar 0)) .default })\n\ntheorem fold_idempotent (e : Expr) : fold (fold e) = fold e :=\n  \
    fold_forged (fold e)"

def candidates : List Candidate := [
  { name := "agent-honest", edits := [(coreCodeFile, appending "\ntheorem ConstantFolding.fold_fold \
      (e : ConstantFolding.Expr) :\n    ConstantFolding.fold (ConstantFolding.fold e) = ConstantFolding.fold e :=\n  \
      ConstantFolding.fold_eq_self_of_normal _ (ConstantFolding.normal_fold e)\n")] },
  { name := "agent-edits-challenge", edits := [(challengeFile, appending "\ntheorem graded : True := trivial\n")] },
  { name := "agent-forges-proof", edits := [(solutionFile, replacing "theorem fold_idempotent (e : Expr) : \
      fold (fold e) = fold e :=\n  fold_eq_self_of_normal (fold e) (normal_fold e)" forged)] },
  { name := "agent-relocks-weakened-statement", edits := weakened, relocks := true }]

def commitCandidate (context : Context) (base : System.FilePath) (candidate : Candidate) : Trial Unit := do
  let fail := s!"the gate cannot commit the candidate {candidate.name} that grade judges"
  succeed (← gitIn base #["checkout", "-q", "-b", candidate.name]) fail "Fix what git reports" next
  applyEdits base source next candidate.edits
  if candidate.relocks then
    IO.FS.removeFile (base / "owned.lock")
    succeed (← context.lakeIn base #["build", ":softwareChallengeStatement"])
      s!"`lake build` cannot re-lock after the edits of {candidate.name}"
      s!"Make the edits of {candidate.name} in {source} build" next
  for args in [#["add", "-A"], #["commit", "-q", "-m", candidate.name], #["checkout", "-q", "base"]] do
    succeed (← gitIn base args) fail "Fix what git reports" next

def prepareBase (context : Context) (base : System.FilePath) : Trial Unit := do
  discard <| TemplateRun.prepare context base next
  for candidate in candidates do commitCandidate context base candidate
  succeed (← context.lakeIn base #["build", "software_challenge/grade", ":softwareChallengeStatement"])
    "grade or the base's statement does not build, so no candidate can be graded"
    "Fix what the output below reports" next

structure Grading where
  case : String
  candidate : String
  code : UInt32
  says : String
  failingSteps : Bool := false
  ordered : Option (String × String) := none

def gradings : List Grading := [
  { case := "an honest candidate", candidate := "agent-honest", code := 0,
    says := "accepted: agent-honest proves every headline" },
  { case := "a candidate that edits Challenge.lean, refused at the owned stage", candidate := "agent-edits-challenge",
    code := 1, says := "agent-edits-challenge changes the owned files" },
  { case := "a proof forged with debug.skipKernelTC, refused by the comparator after the candidate's steps",
    candidate := "agent-forges-proof", code := 1, says := "`lake comparator` rejects agent-forges-proof",
    ordered := some ("ConstantFolding.AddAgrees", "Running Lean default kernel") },
  { case := "a weakened statement re-locked with it, refused at the owned stage",
    candidate := "agent-relocks-weakened-statement", code := 1,
    says := "agent-relocks-weakened-statement changes the owned files" },
  { case := "a candidate whose grade steps fail to start, which grade cannot judge", candidate := "agent-honest",
    code := 3, says := "before judging", failingSteps := true },
  { case := "a commit that does not exist, which grade cannot judge", candidate := "absent", code := 3,
    says := "absent names no commit" }]

def failingLake : String :=
  "#!/bin/sh\ncase \"$(pwd)\" in\n  */.lake/grade/*) echo 'error: simulated failure before judging' >&2; exit 1;;\n\
    esac\nexec \"$REAL_LAKE\" \"$@\"\n"

def positionOf (text marker : String) : Option Nat :=
  match text.splitOn marker with
  | before :: _ :: _ => some before.length
  | _ => none

def words (text : String) : List String :=
  ((String.ofList (text.toList.map fun char => if char.isAlpha then char.toLower else ' ')).splitOn " ").filter
    (!·.isEmpty)

def inOrder (text : String) : Option (String × String) → Bool
  | some (first, second) => match positionOf text first, positionOf text second with
    | some early, some late => early < late
    | _, _ => false
  | none => true

def decides (ran : Ran) (grading : Grading) : Trial Unit := do
  unless inOrder ran.stdout grading.ordered do
    throwThe String s!"`{ran.shown}` in {ran.dir} did not print \"{(grading.ordered.map (·.1)).getD ""}\", from \
      the candidate's `lake test`, before \"{(grading.ordered.map (·.2)).getD ""}\", from `lake comparator`, so \
      grade no longer runs the candidate's build, lint and test before the comparator. Restore that order in judge \
      in SoftwareChallenge/Steps/Grade.lean, then run `{next}`.\n{ran.tail}"
  unless ran.code == grading.code && ran.output.contains grading.says do
    throwThe String s!"`{ran.shown}` exited {ran.code} in {ran.dir}, expected {grading.code} saying \
      \"{grading.says}\", so grade no longer decides {grading.case} as the gate states. Restore what decided it in \
      SoftwareChallenge/Steps/Grade.lean or in the drivers in lakefile.lean; if the guarantee changed on purpose, \
      change `gradings` in {source}. Then run `{next}`.\n{ran.tail}"
  let unconventional := (ran.output.splitOn "\n").filter fun line =>
    (line.startsWith "refused:" || line.startsWith "cannot judge:") &&
      (!line.contains "`lake " || (words line).contains "ask")
  unless unconventional.isEmpty do
    throwThe String s!"`{ran.shown}` in {ran.dir} printed {unconventional}, which name no `lake` command to run next \
      or say \"ask\", so a candidate's author is not told what to do. Give each message of grade in \
      SoftwareChallenge/Steps/Grade.lean the exact fix and the command to run next, then run `{next}`."

def graded (context : Context) (base wrapper : System.FilePath) (grading : Grading) : Trial Unit := do
  let ran ← if grading.failingSteps then
      runShown s!"grade {grading.candidate}" base (context.lsc / ".lake" / "build" / "bin" / "grade").toString
        #[grading.candidate] #[("LAKE", some wrapper.toString), ("REAL_LAKE", some context.lake)]
    else context.lakeIn base #["exe", "grade", grading.candidate]
  decides ran grading

def worktreesRemoved (base : System.FilePath) : Trial Unit := do
  let listed ← gitIn base #["worktree", "list", "--porcelain"]
  succeed listed "the gate cannot list the worktrees grade left behind" "Fix what git reports" next
  let worktrees := ((listed.stdout.splitOn "\n").filter (·.startsWith "worktree ")).length
  let scratch := base / ".lake" / "grade"
  let left ← if ← scratch.pathExists then (·.map (·.fileName)) <$> scratch.readDir else pure #[]
  unless worktrees == 1 && left.isEmpty do
    throwThe String s!"{base} lists {worktrees} worktrees and keeps {left} in .lake/grade after every grade \
      finished, expected 1 and none, so grade leaves checkouts of candidates behind. Make clean in \
      SoftwareChallenge/Steps/Grade.lean remove the worktree and its configuration on every path, then run \
      `{next}`.\n{listed.stdout}"

def replacedJudge : List Edit := [
  ("lakefile.lean", replacing "script lint_challenge do " "script lint_challenge do return 0\n\nscript lint_replaced do "),
  ("Examples" / "ConstantFolding" / coreCodeFile, appending "\ntheorem ConstantFolding.broken : False := rfl\n")]

def judgeReplacement : Grading :=
  { case := "an in-repository candidate that replaces the library's lint driver",
    candidate := "agent-replaces-the-judge", code := 1, says := "`lake build` fails on agent-replaces-the-judge" }

def inRepository (context : Context) (dir : System.FilePath) : Trial Unit := do
  let repository := dir / "inrepo"
  let listed ← gitIn context.lsc #["ls-files", "-z", "--cached", "--others", "--exclude-standard"]
  succeed listed "the gate cannot list the library's files to copy into a repository with the template"
    "Run the gate from a git checkout of the library" next
  for file in (listed.stdout.splitOn "\x00").filter (!·.isEmpty) do
    let path := context.lsc / file
    if (← path.pathExists) && !(← path.isDir) then
      if let some parent := (repository / file).parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile (repository / file) (← IO.FS.readBinFile path)
  let fail := "the gate cannot commit the repository that holds the library and the template"
  for args in [#["init", "-q"], #["add", "-A"], #["commit", "-q", "-m", "base"],
      #["checkout", "-q", "-b", judgeReplacement.candidate]] do
    succeed (← gitIn repository args) fail "Fix what git reports" next
  applyEdits repository source next replacedJudge
  for args in [#["add", "-A"], #["commit", "-q", "-m", judgeReplacement.candidate], #["checkout", "-q", "base"]] do
    succeed (← gitIn repository args) fail "Fix what git reports" next
  let template := repository / "Examples" / "ConstantFolding"
  TemplateRun.requireLocally (← IO.FS.realPath repository) template
  decides (← context.lakeIn template #["exe", "grade", judgeReplacement.candidate]) judgeReplacement
  worktreesRemoved template

def run (context : Context) : IO (Array Outcome) := do
  let dir := context.root / "grade"
  fresh dir
  let inRepositoryTask ← IO.asTask (prio := .dedicated) <|
    check s!"{judgeReplacement.case}: exit {judgeReplacement.code}, and its worktree is removed" next
      (inRepository context dir)
  let base := dir / "base"
  let (setup, ready?) ← attempt "the base, its candidates and grade are built and committed" next
    (prepareBase context base)
  let mut outcomes := #[setup]
  if ready?.isSome then
    let wrapper := dir / "failing-lake"
    IO.FS.writeFile wrapper failingLake
    IO.setAccessRights wrapper { user := { read := true, write := true, execution := true } }
    outcomes := outcomes ++ (← concurrently context.jobs (gradings.toArray.map fun grading =>
      check s!"{grading.case}: exit {grading.code}" next (graded context base wrapper grading)))
    outcomes := outcomes.push (← check "every grade removed its worktree" next (worktreesRemoved base))
  return outcomes.push (← IO.ofExcept inRepositoryTask.get)

end SoftwareChallengeTests.Gate.GradeRun

namespace SoftwareChallengeTests.Gate

open SoftwareChallenge

def runs : List (String × String × (Context → IO (Array Outcome))) := [
  ("template", "R1, the template", TemplateRun.run),
  ("comparator", "R2, the comparator on SoftwareChallengeTests/Comparator", ComparatorRun.run),
  ("grade", "R3, real grades with the template as the base", GradeRun.run)]

def usage : String :=
  s!"usage: `lake exe lsc-gate <run>` runs one real run from the library's root, where <run> is \
    {" or ".intercalate (runs.map (·.1))}; `lake build templateRun`, `lake build comparatorRun` and `lake \
    build gradeRun` run them traced, `lake exe lsc-gate stale` names the stale ones, and `lake exe lsc-gate full` runs \
    all three again."

def contextHere : IO (Except String Context) := do
  let lsc ← IO.FS.realPath (← IO.currentDir)
  unless (← (lsc / "lakefile.lean").pathExists) && (← (lsc / "Examples" / "ConstantFolding").pathExists) do
    return .error s!"{lsc} is not the library's root, which holds lakefile.lean and Examples/ConstantFolding, so the \
      gate has no template to run. Run it from the library's root, as `lake build templateRun` does."
  let root := lsc / ".lake" / "build" / "gate"
  if Sandbox.covers root.toString then
    return .error s!"{root} is under /home, /root, /run, /tmp or /var, which the comparator's sandbox hides, so no \
      comparator run there could judge anything. Clone the library outside those, then run `lake build \
      templateRun` there."
  let threads := min 16 (System.Platform.Internal.getHardwareConcurrency ()).toNat
  let jobs := max 1 (((← IO.getEnv "SOFTWARE_CHALLENGE_JOBS").bind (·.toNat?)).getD threads)
  return .ok { lake := (← IO.getEnv "LAKE").getD "lake", lsc, root, jobs }

def gate (name : String) : IO UInt32 := do
  let some (_, title, run) := runs.find? (·.1 == name) | do IO.eprintln usage; return 2
  match ← contextHere with
  | .error message => IO.eprintln message; return 1
  | .ok context =>
    let start ← IO.monoMsNow
    let outcomes ← run context
    IO.println (report s!"lsc-gate {name}: {title}, in {context.root / name}" outcomes ((← IO.monoMsNow) - start))
    return if outcomes.all fun outcome => (outcome.failure?).isNone then 0 else 1

def targetOf (run : String) : String := s!"{run}Run"

def modifiedSeconds (file : System.FilePath) : IO Int :=
  return (← file.metadata).modified.sec

def testedFor (context : Context) : IO (Option Nat) := do
  let dir := context.lsc / ".lake" / "build" / "softwareChallenge"
  unless (← (dir / "lake.json").pathExists) && (← (dir / "Checks.lean").pathExists) &&
      !(← (dir / "test.status").pathExists) do
    return none
  let began ← modifiedSeconds (dir / "lake.json")
  unless (← modifiedSeconds (dir / "Checks.lean")) ≥ began do return none
  IO.FS.createDirAll context.root
  let clock := context.root / "clock"
  IO.FS.writeFile clock ""
  return some ((← modifiedSeconds clock) - began).toNat

def stale (context : Context) : IO UInt32 := do
  let found ← runs.filterM fun (run, _) => do
    return (← context.lakeIn context.lsc #["build", "--no-build", targetOf run]).code != 0
  unless found.isEmpty do
    IO.println s!"Real runs stale: {", ".intercalate (found.map (targetOf ·.1))}; `lake test -- full` runs them"
  if let some seconds ← testedFor context then IO.println s!"lake test has taken {seconds} s so far"
  return 0

def budget : Nat := 300

def full (context : Context) : IO UInt32 := do
  let before := (← testedFor context).getD 0
  let start ← IO.monoMsNow
  for (run, _) in runs do
    let trace := context.root / s!"{run}.txt.trace"
    if ← trace.pathExists then IO.FS.removeFile trace
  let code ← (← IO.Process.spawn {
    cmd := context.lake, args := #["build"] ++ (runs.map (targetOf ·.1)).toArray, cwd := some context.lsc
    env := unsetForChildren }).wait
  let seconds := ((← IO.monoMsNow) - start) / 1000
  IO.println s!"The full gate took {before + seconds} s: {before} s of `lake test` before the real runs, which took \
    {seconds} s"
  if before + seconds ≤ budget then return code
  IO.eprintln s!"{context.root}: `lake test -- full` took {before + seconds} s, over the {budget} s it may take, so \
    the full gate fails. Make the slowest real run, as its log in {context.root} times it, or the own tests before \
    it faster, then run `lake test -- full`."
  return 1

end SoftwareChallengeTests.Gate

open SoftwareChallengeTests.Gate in
def main : List String → IO UInt32
  | [mode] =>
    if mode == "stale" || mode == "full" then do
      match ← contextHere with
      | .error message => IO.eprintln message; return 1
      | .ok context => if mode == "stale" then stale context else full context
    else gate mode
  | _ => do
    IO.eprintln usage
    return 2
module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Files

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def config : Config :=
  { challenge := `Challenge, solution := `App.Solution, theorems := #[`App.law], definitions := #[`App.hole]
    axioms := standardAxioms }

def scratch : IO System.FilePath := do
  let dir := (← IO.currentDir) / ".lake" / "build" / "readTests" / "files"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll (dir / "dir with space")
  return dir

def lakeIn (dir : System.FilePath) (inputs : Array String) : LakeFacts :=
  { packageDir := dir.toString, configFiles := #["lakefile.lean"]
    modules := #[⟨`App.CoreCode, "App/CoreCode.lean"⟩], challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩]
    defaultExeRoots := #[], packages := #[], defaultTargets := #[], builtinLint := none, testDriver := "software_challenge/test_challenge"
    testDriverArgs := #[], testDriverArgsPlace := ⟨"lakefile.lean", 1⟩, ownTests := #[], inputs }

run_cmd Elab.Command.liftCoreM do
  let dir ← scratch
  IO.FS.writeFile (dir / "lakefile.lean") "import Lake\n"
  IO.FS.writeFile (dir / "Challenge.lean") "module\n"
  IO.FS.writeFile (dir / "dir with space" / "Spec \"quoted\".lean") "module\n"
  IO.FS.writeFile (dir / "owned.lock") "123 lakefile.lean\n456 Challenge.lean\n"
  IO.FS.writeFile (dir / "comparator.json") (Config.render config)
  IO.FS.writeFile (dir / "Secret.lean") "module\n"
  let inputs := #["lakefile.lean", "Challenge.lean", "dir with space/Spec \"quoted\".lean", "Gone.lean", lockFile,
    comparatorFile]
  let lake := lakeIn dir inputs
  let files ← fileFacts lake .build
  check (files.lock == .unreadable lockProblem) s!"owned.lock in the old line format did not read as unreadable"
  check (files.comparator == .decoded config) "comparator.json as `lake build` writes it did not decode"
  check (files.digests.map (·.path) == #["lakefile.lean", "Challenge.lean", "dir with space/Spec \"quoted\".lean"])
    s!"the digests did not cover exactly the readable inputs other than owned.lock and comparator.json: \
      {files.digests.map (·.path)}"
  check (files.digests[0]?.map (·.digest) == some (toString (hash "import Lake\n")))
    "a digest is not the decimal hash of the file's text"
  let entries : Array Lock.Entry := #[⟨"lakefile.lean", "1"⟩, ⟨"dir with space/Spec \"quoted\".lean", "2"⟩]
  IO.FS.writeFile (dir / "owned.lock") (Lock.render entries)
  check ((← fileFacts lake .build).lock == .decoded entries) "owned.lock as `lake build` records it did not decode"
  IO.FS.removeFile (dir / "owned.lock")
  IO.FS.writeFile (dir / "comparator.json") "{}"
  let missing ← fileFacts lake .build
  check (missing.lock == .missing && missing.comparator == .unreadable comparatorProblem)
    "a missing owned.lock or an unreadable comparator.json was misread"
  let outside ← refusal (discard (readInput lake "Secret.lean" .lint))
  check (outside.any fun message => contains message "Secret.lean:1: lake.json does not list it among the inputs" &&
      contains message "no edit to the package fixes this" && contains message "SoftwareChallenge's lakefile.lean" &&
      contains message "then run `lake lint`.")
    s!"a path outside the inputs was read: {outside}"
  let unlisted ← refusal (discard (fileFacts (lakeIn dir #["lakefile.lean"]) .build))
  check (unlisted.any (contains · s!"{lockFile}:1: lake.json does not list it"))
    s!"owned.lock was read though the inputs do not list it: {unlisted}"
  let unnamed ← refusal (discard (readSource lake "Secret.lean" .test))
  check (unnamed.any fun message => contains message "names it neither as an input nor as a module's file" &&
      contains message "no edit to the package fixes this" && contains message "then run `lake test`.")
    s!"a source that lake.json does not name was read: {unnamed}"
  check ((← readSource lake "App/CoreCode.lean" .build) == "") "a module file that does not exist did not read as empty"

run_cmd Elab.Command.liftCoreM do
  let file := "SoftwareChallengeTests/Fixtures/Challenge.lean"
  let lines ← importLines (fixture `Challenge) file (← IO.FS.readFile file)
  check (lines.map (fun line => (line.fact.name, line.fact.comptime, line.fact.line, line.text)) ==
      #[(fixture `CoreCode, false, 3, "public import SoftwareChallengeTests.Fixtures.CoreCode"),
        (`SoftwareChallenge, true, 4, "meta import SoftwareChallenge")])
    s!"the import lines were misread from the header: {lines.map (·.text)}"
  let header := "module\n\n-- a comment\npublic import A.B -- a trailing comment\n\nmeta import C.D\nimport all E\n"
  let read ← importLines `M "M.lean" header
  check (read.map (fun line => (line.fact.name, line.fact.comptime, line.fact.line)) ==
      #[(`A.B, false, 4), (`C.D, true, 6), (`E, false, 7)])
    s!"import positions were misread around comments: {read.map (·.fact.line)}"
  check (read[0]?.map (·.text) == some "public import A.B -- a trailing comment")
    "an import line was not quoted whole"

end

end SoftwareChallengeReadTests.Files

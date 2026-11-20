module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Lake

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def sample : LakeFacts := {
  packageDir := "/work/a package", configFiles := #["lakefile.lean", "lean-toolchain"]
  modules := #[⟨`App.CoreCode, "App/CoreCode.lean"⟩, ⟨`App.«weird name», "App/weird name.lean"⟩]
  challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩], defaultExeRoots := #[`App.WorldCode]
  packages := #[{ name := `lib, configured := "/work/lib", real := "/real/lib", overridden := true }]
  defaultTargets := #[`App, `statement]
  builtinLint := some ⟨"lakefile.lean", 4⟩, lintDriver := "software_challenge/lint_challenge"
  testDriver := "software_challenge/test_challenge"
  testDriverArgs := #["own_test"], testDriverArgsPlace := ⟨"lakefile.lean", 6⟩
  ownTests := #[⟨"own_test", .script, ⟨"lakefile.lean", 8⟩⟩], inputs := #["lakefile.lean", "owned.lock"] }

def written : String := "{\"packageDir\": \"/work/a package\",
  \"configFiles\": [\"lakefile.lean\", \"lean-toolchain\"],
  \"modules\": [{\"module\": \"App.CoreCode\", \"file\": \"App/CoreCode.lean\"},
    {\"module\": \"App.«weird name»\", \"file\": \"App/weird name.lean\"}],
  \"challengeCandidates\": [{\"module\": \"Challenge\", \"file\": \"Challenge.lean\"}],
  \"defaultExeRoots\": [\"App.WorldCode\"],
  \"packages\": [{\"name\": \"lib\", \"configured\": \"/work/a package/../lib/.\", \"real\": \"/real/lib\",
    \"overridden\": true}],
  \"defaultTargets\": [\"App\", \"statement\"], \"builtinLint\": true,
  \"lintDriver\": \"software_challenge/lint_challenge\",
  \"testDriver\": \"software_challenge/test_challenge\", \"testDriverArgs\": [\"own_test\"],
  \"ownTests\": [{\"name\": \"own_test\", \"kind\": \"script\"}],
  \"inputs\": [\"lakefile.lean\", \"owned.lock\"]}"

def config : String :=
  "import Lake\nopen Lake DSL\npackage app where\n  builtinLint := true\n  leanOptions := #[]\n\
    testDriverArgs := #[\"own_test\"]\n\nscript own_test do\n  return 0\n"

def parsed (text : String) : Option LakeFacts :=
  match parseLake text with
  | .ok lake => some (lake.facts config)
  | .error _ => none

run_cmd Elab.Command.liftCoreM do
  check (parsed written == some sample) "the JSON object a lakefile writes did not read as the Lake facts it names"
  let bare := { sample with builtinLint := none, lintDriver := "" }
  check (parsed ((written.replace "\"builtinLint\": true" "\"builtinLint\": false").replace
      "\"lintDriver\": \"software_challenge/lint_challenge\"" "\"lintDriver\": \"\"") == some bare)
    "Lake facts without builtinLint or lintDriver did not read back"
  check (Statement.setupOf sample == #[.builtinLint ⟨"lakefile.lean", 4⟩] &&
      Statement.setupOf bare == #[.lintDriver ""])
    s!"the setup problems of the Lake facts were misjudged: {repr (Statement.setupOf bare)}"
  match parseLake (written.replace "\"inputs\"" "\"outputs\"") with
  | .ok _ => throwError "Lake facts without inputs were accepted"
  | .error problem => check (contains problem "inputs") s!"a missing field was not named: {problem}"
  let broken := (← IO.currentDir) / ".lake" / "build" / "readTests" / "lake.json"
  IO.FS.createDirAll (broken.parent.getD ".")
  IO.FS.writeFile broken "{\"packageDir\": 1}"
  let refused ← refusal (discard (loadLake broken .lint))
  check (refused.any fun message => contains message s!"{broken}:1: it is not the JSON object of Lake facts" &&
      contains message s!"Delete {broken} and run `lake build`, then run `lake lint`.")
    s!"an unreadable lake.json was not refused with its fix: {refused}"

end

end SoftwareChallengeReadTests.Lake

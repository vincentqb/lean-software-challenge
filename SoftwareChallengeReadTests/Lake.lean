module

meta import SoftwareChallengeReadTests.Support

namespace SoftwareChallengeReadTests.Lake

meta section

open Lean SoftwareChallenge SoftwareChallenge.Read SoftwareChallengeReadTests

def sample : LakeFacts := {
  packageDir := "/work/a package", repository? := some "/work", configFiles := #["lakefile.lean", "lean-toolchain"]
  modules := #[⟨`App.CoreCode, "App/CoreCode.lean"⟩, ⟨`App.«weird name», "App/weird name.lean"⟩]
  challengeCandidates := #[⟨`Challenge, "Challenge.lean"⟩], exeRoots := #[`App.WorldCode]
  packages := #[⟨`lib, "../lib", "/real/lib"⟩], defaultTargets := #[`App, `statement]
  builtinLint := some ⟨"lakefile.lean", 4⟩, testDriver := "software_challenge/test_challenge"
  testDriverArgs := #["own_test"], testDriverArgsPlace := ⟨"lakefile.lean", 6⟩
  ownTests := #[⟨"own_test", .script, ⟨"lakefile.lean", 20⟩⟩], inputs := #["lakefile.lean", "owned.lock"] }

def written : String := "{\"packageDir\": \"/work/a package\", \"repository\": \"/work\",
  \"configFiles\": [\"lakefile.lean\", \"lean-toolchain\"],
  \"modules\": [{\"module\": \"App.CoreCode\", \"file\": \"App/CoreCode.lean\"},
    {\"module\": \"App.«weird name»\", \"file\": \"App/weird name.lean\"}],
  \"challengeCandidates\": [{\"module\": \"Challenge\", \"file\": \"Challenge.lean\"}],
  \"exeRoots\": [\"App.WorldCode\"],
  \"packages\": [{\"name\": \"lib\", \"configured\": \"../lib\", \"real\": \"/real/lib\"}],
  \"defaultTargets\": [\"App\", \"statement\"], \"builtinLint\": {\"file\": \"lakefile.lean\", \"line\": 4},
  \"testDriver\": \"software_challenge/test_challenge\", \"testDriverArgs\": [\"own_test\"],
  \"testDriverArgsPlace\": {\"file\": \"lakefile.lean\", \"line\": 6},
  \"ownTests\": [{\"name\": \"own_test\", \"kind\": \"script\",
    \"place\": {\"file\": \"lakefile.lean\", \"line\": 20}}],
  \"inputs\": [\"lakefile.lean\", \"owned.lock\"]}"

def parsed (text : String) : Option LakeFacts :=
  match parseLake text with
  | .ok lake => some lake
  | .error _ => none

run_cmd Elab.Command.liftCoreM do
  check (parsed (renderLake sample) == some sample) "renderLake does not read back through parseLake"
  check (parsed written == some sample) "the JSON object a lakefile writes did not read as the Lake facts it names"
  let bare := { sample with repository? := none, builtinLint := none }
  check (parsed (renderLake bare) == some bare) "Lake facts without a repository or builtinLint did not read back"
  check (contains (renderLake bare) "\"builtinLint\": null" && !contains (renderLake bare) "\"repository\"")
    s!"an absent repository or builtinLint was rendered otherwise than omitted and null: {renderLake bare}"
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

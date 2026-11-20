module

meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures.Rendezvous

def place : IO System.FilePath :=
  return (← IO.currentDir) / ".lake" / "rendezvous" / toString (← IO.Process.getPID)

def meet (mine theirs : String) : IO Unit := do
  let dir ← place
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / mine) ""
  let mut waited := 0
  while !(← (dir / theirs).pathExists) do
    if waited ≥ 20000 then
      throw (IO.userError s!"{theirs} did not arrive within 20 s, so the Checks ran one after the other")
    IO.sleep 100
    waited := waited + 100

WorldClaim Meets := True

Check Meets := meet "first" "second"

Check Meets := meet "second" "first"

end SoftwareChallengeTests.Fixtures.Rendezvous

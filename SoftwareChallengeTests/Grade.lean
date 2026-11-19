module

meta import SoftwareChallenge.Grade

namespace SoftwareChallengeTests.Grade

open SoftwareChallenge.Grade

meta def missingTheorem : IO.Process.Output := { exitCode := 1, stdout := "", stderr :=
  "PANIC at LeanExport.dumpConstant LeanExport.Basic:254:48: Constant A.b_rejects not found in environment.\n\
  error: Child exited with 134\n" }

meta def crashed : IO.Process.Output := { exitCode := 1, stdout := "", stderr := "error: Child exited with 134\n" }

meta def hiddenByBwrap : IO.Process.Output := { exitCode := 1, stdout := "", stderr :=
  "bwrap: Can't bind mount /home\nPANIC at LeanExport.dumpConstant LeanExport.Basic:254:48: Constant A.b \
  not found in environment.\n" }

#guard missingConstant? missingTheorem.stderr == some "A.b_rejects"
#guard (rejection? missingTheorem).any (·.startsWith "the solution does not declare A.b_rejects")
#guard (rejection? crashed).isNone
#guard (rejection? hiddenByBwrap).isNone

end SoftwareChallengeTests.Grade

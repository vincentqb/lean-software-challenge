module

meta import SoftwareChallenge.CoreSpec.Grade
meta import SoftwareChallenge.CoreSpec.Package
meta import SoftwareChallenge.CoreCode.Grade
meta import SoftwareChallenge.Steps.Grade

meta section

namespace SoftwareChallengeTests.Grade

open Lean SoftwareChallenge

def observed (stage : Stage) (verdict : Verdict := .accept) : Observation := { stage, verdict, detail := "" }

#guard Grade.decide (Stage.order.map observed) == .accept

#guard Grade.decide [] == .cannotJudge

#guard Grade.decide ((Stage.order.map observed).drop 1) == .cannotJudge

#guard Grade.decide (Stage.order.map observed ++ [observed .test]) == .cannotJudge

#guard Grade.decide [observed .lock, observed .statement, observed .owned .refuse] == .refuse

#guard Grade.decide [observed .lock, observed .owned .cannotJudge, observed .comparator .refuse] == .cannotJudge

#guard Grade.decide (Stage.order.map fun stage => observed stage (if stage == .comparator then .refuse else .accept)) ==
  .refuse

def solution : Name := `ConstantFolding.Solution

def building : String := "Resolving dependencies\nBuilding ConstantFolding.Solution\n"

def exported : String := building ++ "Build completed successfully (72 jobs).\n\
  Exporting #[ConstantFolding.fold_idempotent] from ConstantFolding.Solution\n"

def judged (output : String) : Verdict := Comparator.classify solution 1 output

def rejected (output : String) : Option Comparator.Rejection := Comparator.rejection? solution 1 output

#guard Comparator.classify solution 0 (exported ++ "Running Lean default kernel on solution\n\
  Lean default kernel accepts the solution\nYour solution is okay!\n") == .accept

#guard Comparator.classify solution 0 "Uses no axioms\n" == .accept

#guard rejected (exported ++ "error: Const not found in solution: 'ConstantFolding.fold'") == some .absent

#guard rejected (exported ++ "error: Const not found in solution 'ConstantFolding.eval'") == some .absent

#guard rejected (exported ++ "error: Challenge and solution constant kind don't match: 'ConstantFolding.fold'") ==
  some .kind

#guard rejected (exported ++ "error: Challenge and solution theorem statement do not match: 'ConstantFolding.f'") ==
  some .statement

#guard rejected (exported ++ "error: Solution constant is not a definition: 'ConstantFolding.fold'") ==
  some .notDefinition

#guard rejected (exported ++ "error: Const does not match between challenge and target 'ConstantFolding.eval'") ==
  some .differs

#guard rejected (exported ++ "error: Constant not found in solution 'ConstantFolding.helper'") == some .unexported

#guard rejected (exported ++ "error: Illegal axiom detected: 'ConstantFolding.cheat'") == some .axiomUsed

#guard rejected (exported ++ "error: Solution constant is not a theorem: 'ConstantFolding.fold_idempotent'") ==
  some .notTheorem

#guard rejected "error: Axiom 'ConstantFolding.cheat' is not permitted; it is used by 'ConstantFolding.f'" ==
  some .axiomUsed

#guard rejected (exported ++ "Running Lean default kernel on solution\nLean default kernel rejected the solution\n\
  error: Lean default exited with 1") == some .kernel

#guard judged (exported ++ "Running Lean default kernel on solution\nLean default kernel rejected the solution\n\
  error: Lean default exited with 137") == .cannotJudge

#guard judged (exported ++ "Running Lean default kernel on solution\n\
  Error while interacting with Lean default kernel\n\
  error: Error while interacting with Lean default kernel: no such file") == .cannotJudge

#guard judged (exported ++ "error: Const not found in challenge: 'ConstantFolding.fold'") == .cannotJudge

#guard judged (exported ++ "error: Const not found in challenge 'ConstantFolding.eval'") == .cannotJudge

#guard judged (exported ++ "error: Challenge constant is not a definition: 'ConstantFolding.fold'") == .cannotJudge

#guard rejected (building ++ "error: ConstantFolding/CoreCode.lean:7:0: Type mismatch\nerror: build failed\n\
  error: Child exited with 1") == some .unbuilt

#guard judged "Resolving dependencies\nBuilding Challenge\nerror: ConstantFolding/CoreSpec.lean:3:0: unknown\n\
  error: build failed\nerror: Child exited with 1" == .cannotJudge

#guard judged (exported ++ "error: Child exited with 1") == .cannotJudge

#guard judged "Resolving dependencies\nerror: Child exited with 1" == .cannotJudge

#guard judged (building ++ "error: build failed\nerror: Child exited with 137") == .cannotJudge

#guard judged (building ++ "error: external command '/toolchain/bin/clang' exited with code 1\n\
  error: build failed\nerror: Child exited with 1") == .cannotJudge

#guard judged (building ++ "error: failed to write '/lib/.lake/build/A.olean': read-only file system\n\
  error: Child exited with 1") == .cannotJudge

#guard judged "bwrap: Can't bind mount /oldroot/tmp on /newroot/tmp: Unable to mount source on destination" ==
  .cannotJudge

#guard judged "Resolving dependencies\nerror: `lake env` did not report the project's search path" == .cannotJudge

#guard Comparator.classify solution 2 "error: malformed configuration in 'comparator.json': unexpected end" ==
  .cannotJudge

#guard Comparator.classify solution 2 "error: nothing to check: the configuration names no theorems or definitions" ==
  .cannotJudge

#guard Comparator.classify solution 2 "error: `lake comparator` needs `bwrap` to sandbox the code it checks" ==
  .cannotJudge

#guard Comparator.classify solution 2 (exported ++ "error: Challenge and solution theorem statement do not match") ==
  .cannotJudge

#guard Comparator.retryable 1 "bwrap: Can't bind mount /oldroot/ on /newroot/: Resource busy"

#guard !Comparator.retryable 0 "bwrap: Can't bind mount /oldroot/ on /newroot/: Resource busy"

#guard !Comparator.retryable 1 "error: Child exited with 1"

def template : Config where
  challenge := `Challenge
  solution := `ConstantFolding.Solution
  theorems := #[`ConstantFolding.fold_idempotent]
  definitions := #[`ConstantFolding.fold]
  axioms := standardAxioms

#guard Comparator.exportTargets template ==
  #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind, `ConstantFolding.fold_idempotent] ++ standardAxioms ++
    Comparator.primitiveTargets ++ #[`ConstantFolding.fold]

#guard Comparator.exportTargets { template with axioms := #[``propext] } ==
  #[`ConstantFolding.fold_idempotent, ``propext] ++ Comparator.primitiveTargets ++ #[`ConstantFolding.fold]

#guard Comparator.primitiveTargets.size == 26

#guard Sandbox.covers "/home/user/lean"

#guard Sandbox.covers "/tmp"

#guard Sandbox.covers "/var/lib/x"

#guard Sandbox.covers "/run/user/1000"

#guard Sandbox.covers "/root/.elan"

#guard !Sandbox.covers "/homework"

#guard !Sandbox.covers "/local/home/user/lean"

#guard !Sandbox.covers "/opt/lean"

def packages : Array (Name × String) := #[
  (`software_challenge, "/w/repo"),
  (`plausible, "/w/repo/Examples/ConstantFolding/.lake/packages/plausible"),
  (`vendored, "/w/repo/Examples/ConstantFolding/vendor/dep"),
  (`sibling, "/w/repo/lib/"),
  (`hidden, "/tmp/hidden"),
  (`home, "/home/user/dep"),
  (`outside, "/opt/dep"),
  (`materialized, "/w/repo/.lake/grade/1/Examples/ConstantFolding/.lake/packages/x")]

def checkout : String := "/w/repo/.lake/grade/1/Examples/ConstantFolding"

#guard (Sandbox.classify checkout (some "/w/repo") packages).map (·.placement) ==
  #[.insideRepository, .ok, .insideRepository, .insideRepository, .hidden, .hidden, .ok, .ok]

#guard (Sandbox.classify checkout none packages).map (·.placement) ==
  #[.ok, .ok, .ok, .ok, .hidden, .hidden, .ok, .ok]

#guard (Sandbox.classify "/home/user/package" none #[(`local, "/home/user/package/.lake/packages/local")]).map
  (·.placement) == #[.ok]

def lock : Array Lock.Entry := #[{ path := "Challenge.lean", digest := "1" },
  { path := "ConstantFolding/CoreSpec.lean", digest := "2" }]

#guard Grade.ownedPathspecs "Examples/ConstantFolding/" "/w/repo" lock
    (Sandbox.classify checkout (some "/w/repo") packages) == #[
  #[":(top,literal)Examples/ConstantFolding/Challenge.lean",
    ":(top,literal)Examples/ConstantFolding/ConstantFolding/CoreSpec.lean",
    ":(top,literal)Examples/ConstantFolding/owned.lock"],
  #[":(top,literal)", ":(top,literal,exclude)Examples/ConstantFolding"],
  #[":(top,literal)Examples/ConstantFolding/vendor/dep"],
  #[":(top,literal)lib"]]

#guard Grade.ownedPathspecs "" "/w/repo" #[{ path := "a b/x*.lean", digest := "3" }] #[] ==
  #[#[":(top,literal)a b/x*.lean", ":(top,literal)owned.lock"]]

#guard Grade.ownedPathspecs "" "/w/repo" #[] #[{ name := `self, dir := "/w/repo", placement := .insideRepository }] ==
  #[#[":(top,literal)owned.lock"]]

#guard Steps.Grade.lockEntries "14750095111711872102 lakefile.lean\n4606896722634636308 Challenge.lean" ==
  some #[{ path := "lakefile.lean", digest := "14750095111711872102" },
    { path := "Challenge.lean", digest := "4606896722634636308" }]

#guard Steps.Grade.lockEntries "12 a path with spaces.lean" ==
  some #[{ path := "a path with spaces.lean", digest := "12" }]

#guard Steps.Grade.lockEntries (Lock.render lock) == some lock

#guard Steps.Grade.lockEntries "not a lock" == none

#guard Steps.Grade.quoted "it's" == "'it'\\''s'"

end SoftwareChallengeTests.Grade

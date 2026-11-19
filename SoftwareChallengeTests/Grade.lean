module

meta import SoftwareChallenge.CoreSpec.Grade
meta import SoftwareChallenge.CoreCode.Grade
meta import SoftwareChallenge.Steps.Grade

meta section

namespace SoftwareChallengeTests.Grade

open Lean SoftwareChallenge

def observed (stage : Stage) (verdict : Verdict := .accept) : Observation := { stage, verdict, detail := "" }

#guard Grade.decide (Stage.order.map observed) == .accept

#guard Grade.decide [] == .cannotJudge

#guard Grade.decide ((Stage.order.map observed).drop 1) == .cannotJudge

#guard Grade.decide (Stage.order.map observed ++ [observed .comparator]) == .cannotJudge

#guard Grade.decide [observed .lock, observed .statement, observed .owned .refuse] == .refuse

#guard Grade.decide [observed .lock, observed .owned .cannotJudge, observed .comparator .refuse] == .cannotJudge

#guard Grade.decide (Stage.order.map fun stage => observed stage (if stage == .comparator then .refuse else .accept)) ==
  .refuse

#guard Stage.order.getLast? == some .comparator

#guard Grade.decide ((Stage.order.takeWhile (· != .lint)).map observed ++ [observed .lint .refuse]) == .refuse

def building : String := "Resolving dependencies\nBuilding ConstantFolding.Solution\n"

def exported : String := building ++ "Build completed successfully (72 jobs).\n\
  Exporting #[ConstantFolding.fold_idempotent] from ConstantFolding.Solution\n"

def judged (output : String) : Verdict := Comparator.classify 1 output

def rejected (output : String) : Option Comparator.Rejection := Comparator.rejection? 1 output

#guard Comparator.classify 0 (exported ++ "Running Lean default kernel on solution\n\
  Lean default kernel accepts the solution\nYour solution is okay!\n") == .accept

#guard Comparator.classify 0 "Uses no axioms\n" == .accept

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

#guard judged (building ++ "error: ConstantFolding/CoreCode.lean:7:0: Type mismatch\nerror: build failed\n\
  error: Child exited with 1") == .cannotJudge

#guard judged "Resolving dependencies\nBuilding Challenge\nerror: ConstantFolding/CoreSpec.lean:3:0: unknown\n\
  error: build failed\nerror: Child exited with 1" == .cannotJudge

#guard judged (exported ++ "error: Child exited with 1") == .cannotJudge

#guard judged "Resolving dependencies\nerror: Child exited with 1" == .cannotJudge

#guard judged (building ++ "error: build failed\nerror: Child exited with 137") == .cannotJudge

#guard judged (building ++ "✖ [70/78] Building ConstantFolding.Solution (2.1s)\nerror: Lean exited with code 137\n\
  Some required targets logged failures:\n- ConstantFolding.Solution\nerror: build failed\nerror: Child exited with 1\n") ==
  .cannotJudge

#guard judged (building ++ "✖ [70/78] Building ConstantFolding.Solution\nerror: ConstantFolding/Solution.lean: failed \
  to write '.lake/build/lib/lean/ConstantFolding/Solution.olean': No space left on device (error code: 28)\n\
  error: build failed\nerror: Child exited with 1\n") == .cannotJudge

#guard judged (building ++ "error: ConstantFolding/Solution.lean:1:0: object file \
  /w/base/.lake/packages/x/.lake/build/lib/lean/X.olean of module X does not exist\nerror: build failed\n\
  error: Child exited with 1\n") == .cannotJudge

#guard judged (building ++ "error: external command '/toolchain/bin/clang' exited with code 1\n\
  error: build failed\nerror: Child exited with 1") == .cannotJudge

#guard judged (building ++ "error: failed to write '/lib/.lake/build/A.olean': read-only file system\n\
  error: Child exited with 1") == .cannotJudge

#guard rejected (building ++ "warning: could not write cache: Read-only file system\n\
  Build completed successfully (72 jobs).\nExporting #[ConstantFolding.fold_idempotent] from ConstantFolding.Solution\n\
  error: Challenge and solution theorem statement do not match: 'ConstantFolding.fold_idempotent'\n") ==
  some .statement

#guard judged "bwrap: Can't bind mount /oldroot/tmp on /newroot/tmp: Unable to mount source on destination" ==
  .cannotJudge

#guard judged "Resolving dependencies\nerror: `lake env` did not report the project's search path" == .cannotJudge

#guard Comparator.classify 2 "error: malformed configuration in 'comparator.json': unexpected end" ==
  .cannotJudge

#guard Comparator.classify 2 "error: nothing to check: the configuration names no theorems or definitions" ==
  .cannotJudge

#guard Comparator.classify 2 "error: `lake comparator` needs `bwrap` to sandbox the code it checks" ==
  .cannotJudge

#guard Comparator.classify 2 (exported ++ "error: Challenge and solution theorem statement do not match") ==
  .cannotJudge

def missingWitness : String := "Resolving dependencies\n\
  Building Challenge\n\
  Build completed successfully (30 jobs).\n\
  Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, ConstantFolding.fold_preserves_meaning, \
  ConstantFolding.fold_closed_literal, ConstantFolding.fold_normalizes, ConstantFolding.fold_idempotent, \
  ConstantFolding.fold_keeps_literal, ConstantFolding.output_correct, \
  ConstantFolding.fold_preserves_meaning_rejects_constant, ConstantFolding.fold_closed_literal_rejects_identity, \
  ConstantFolding.fold_normalizes_rejects_identity, ConstantFolding.fold_idempotent_rejects_increment, \
  ConstantFolding.fold_keeps_literal_rejects_zero, ConstantFolding.fold_keeps_literal_applies, \
  ConstantFolding.output_correct_rejects_suffix, propext, Classical.choice, Quot.sound, Nat.add, Nat.sub, Nat.mul, \
  Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, \
  String.ofList, Char.ofNat, List, eagerReduce, Nat, String, String.mk, Char, optParam, autoParam, semiOutParam, \
  outParam, ConstantFolding.fold, ConstantFolding.output] from Challenge\n\
  Building ConstantFolding.Solution\n\
  Build completed successfully (26 jobs).\n\
  Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, ConstantFolding.fold_preserves_meaning, \
  ConstantFolding.fold_closed_literal, ConstantFolding.fold_normalizes, ConstantFolding.fold_idempotent, \
  ConstantFolding.fold_keeps_literal, ConstantFolding.output_correct, \
  ConstantFolding.fold_preserves_meaning_rejects_constant, ConstantFolding.fold_closed_literal_rejects_identity, \
  ConstantFolding.fold_normalizes_rejects_identity, ConstantFolding.fold_idempotent_rejects_increment, \
  ConstantFolding.fold_keeps_literal_rejects_zero, ConstantFolding.fold_keeps_literal_applies, \
  ConstantFolding.output_correct_rejects_suffix, propext, Classical.choice, Quot.sound, Nat.add, Nat.sub, Nat.mul, \
  Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, \
  String.ofList, Char.ofNat, List, eagerReduce, Nat, String, String.mk, Char, optParam, autoParam, semiOutParam, \
  outParam, ConstantFolding.fold, ConstantFolding.output] from ConstantFolding.Solution\n\
  PANIC at LeanExport.dumpConstant LeanExport.Basic:254:48: Constant ConstantFolding.fold_keeps_literal_applies \
  not found in environment.\n\
  backtrace:\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9621e05) \
  [0x7faa737d6e05]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9618987) \
  [0x7faa737cd987]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(lean_panic_fn_borrowed+0x2b) \
  [0x7faa737cda6b]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanexport(panic spec at \
  LeanExport.dumpConstant+0x279) [0x56131c6c52c9]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanexport(List.forIn'.loop [arity↓] spec at \
  LeanExport.dumpEnv+0x262) [0x56131c6de322]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanexport(LeanExport.dumpEnv [λ]+0x167) \
  [0x56131c6de797]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanexport(LeanExport.dumpEnv [boxed, \
  λ]+0x13) [0x56131c6de9f3]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(<apply/3>+0x970) \
  [0x7faa737de4d0]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanexport(LeanExport.M.run [arity↓]+0x33) \
  [0x56131c6b6dd3]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x9616367) \
  [0x7faa737cb367]\n\
  /local/home/quennv/.elan/toolchains/leanprover--lean4---v4.35.0/bin/../lib/lean/libleanshared.so(+0x96169da) \
  [0x7faa737cb9da]\n\
  /lib64/libpthread.so.0(+0x744b) [0x7faa69bf144b]\n\
  /lib64/libc.so.6(clone+0x3f) [0x7faa69ef752f]\n\
  error: Child exited with 134\n"

#guard Comparator.missingConstant? missingWitness == some "ConstantFolding.fold_keeps_literal_applies"

#guard rejected missingWitness == some (.missing "ConstantFolding.fold_keeps_literal_applies")

#guard judged "error: Child exited with 134\n" == .cannotJudge

#guard judged ("bwrap: Can't bind mount /home\n" ++ missingWitness) == .cannotJudge

#guard Comparator.signalled "error: Child exited with 134"

#guard Comparator.signalled "error: Lean exited with code 137"

#guard !Comparator.signalled "error: external command '/toolchain/bin/clang' exited with code 1"

#guard !Comparator.signalled "error: Lean default exited with 1"

#guard Comparator.retryable 1 "bwrap: Can't bind mount /oldroot/ on /newroot/: Resource busy"

#guard !Comparator.retryable 0 "bwrap: Can't bind mount /oldroot/ on /newroot/: Resource busy"

#guard !Comparator.retryable 1 "error: Child exited with 1"

#guard Sandbox.covers "/home/user/lean"

#guard Sandbox.covers "/tmp"

#guard Sandbox.covers "/var/lib/x"

#guard Sandbox.covers "/run/user/1000"

#guard Sandbox.covers "/root/.elan"

#guard !Sandbox.covers "/homework"

#guard !Sandbox.covers "/local/home/user/lean"

#guard !Sandbox.covers "/opt/lean"

#guard Sandbox.within "/w/repo/Examples/ConstantFolding/.lake/packages/x" "/w/repo/"

#guard !Sandbox.within "/w/repository" "/w/repo"

def lock : Array Lock.Entry := #[{ path := "Challenge.lean", digest := "1" },
  { path := "ConstantFolding/CoreSpec.lean", digest := "2" }]

#guard Grade.ownedPathspecs "Examples/ConstantFolding/" lock == #[
  ":(top,literal)Examples/ConstantFolding/Challenge.lean",
  ":(top,literal)Examples/ConstantFolding/ConstantFolding/CoreSpec.lean",
  ":(top,literal)Examples/ConstantFolding/owned.lock"]

#guard Grade.ownedPathspecs "" #[{ path := "a b/x*.lean", digest := "3" }] ==
  #[":(top,literal)a b/x*.lean", ":(top,literal)owned.lock"]

#guard Steps.Grade.lockEntries "14750095111711872102 lakefile.lean\n4606896722634636308 Challenge.lean" ==
  some #[{ path := "lakefile.lean", digest := "14750095111711872102" },
    { path := "Challenge.lean", digest := "4606896722634636308" }]

#guard Steps.Grade.lockEntries "12 a path with spaces.lean" ==
  some #[{ path := "a path with spaces.lean", digest := "12" }]

#guard Steps.Grade.lockEntries (Lock.render lock) == some lock

#guard Steps.Grade.lockEntries "not a lock" == none

#guard ((Steps.Grade.BaseFacts.parse "{\"version\": \"1.3.0\", \"packages\": [{\"type\": \"path\", \
  \"name\": \"software_challenge\", \"dir\": \"/w/repo\"}]}").toOption.map (·.packages)) ==
  some #[(`software_challenge, "/w/repo")]

#guard (Steps.Grade.BaseFacts.parse "{\"version\": \"1.3.0\"}").toOption.isNone

#guard Steps.Grade.quoted "it's" == "'it'\\''s'"

end SoftwareChallengeTests.Grade

module

@[expose] public section

namespace SoftwareChallenge

inductive Stage where
  | lock | statement | owned | dependencies | worktree | comparator | build | lint | test
  deriving DecidableEq, Repr, Inhabited

def Stage.order : List Stage :=
  [.lock, .statement, .owned, .dependencies, .worktree, .comparator, .build, .lint, .test]

inductive Verdict where
  | accept | refuse | cannotJudge
  deriving DecidableEq, Repr, Inhabited

def Verdict.code : Verdict → UInt32
  | .accept => 0
  | .refuse => 1
  | .cannotJudge => 3

structure Observation where
  stage : Stage
  verdict : Verdict
  detail : String
  deriving DecidableEq, Repr, Inhabited

end SoftwareChallenge

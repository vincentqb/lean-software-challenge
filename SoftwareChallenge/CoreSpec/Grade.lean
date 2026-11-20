module

@[expose] public section

namespace SoftwareChallenge

inductive Stage where
  | lock | statement | owned | dependencies | worktree | build | lint | test | comparator
  deriving DecidableEq

def Stage.order : List Stage :=
  [.lock, .statement, .owned, .dependencies, .worktree, .build, .lint, .test, .comparator]

inductive Verdict where
  | accept | refuse | cannotJudge
  deriving DecidableEq

def Verdict.code : Verdict → UInt32
  | .accept => 0
  | .refuse => 1
  | .cannotJudge => 3

structure Observation where
  stage : Stage
  verdict : Verdict
  detail : String

end SoftwareChallenge

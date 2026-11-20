namespace SoftwareChallenge

inductive Rule where
  | kill | killShape | witness | consistent | terminates
  | pending | axiomUsed | impure | fixpoint | unreached | untested
  | owned
  deriving BEq

structure Problem where
  rule : Rule
  place : String
  what : String
  why : String
  fix : String
  next : String

def Problem.render (problem : Problem) : String :=
  s!"{problem.place}: {problem.what}, {problem.why}. {problem.fix}, then run `{problem.next}`."

def placeOf (file : String) (line : Nat) : String := s!"{file}:{line}"

end SoftwareChallenge

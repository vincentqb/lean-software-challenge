module

public import SoftwareChallenge.CoreCode.Facts

public section

namespace SoftwareChallenge

open Lean

inductive OwnedFile where
  | lakefile | manifest | toolchain | challenge
  | specModule (module : Name)
  deriving BEq, Repr, Inhabited

namespace Statement

inductive Error where
  | duplicate (later earlier : Name)
  | mentionsNothing (headline : Name)
  | noKill (headline : Name) (suggestion? : Option String)
  | unmarkedKill (headline kill : Name)
  | killOfNonHeadline (kill named : Name)
  | killReplacesNothing (kill headline : Name)
  | misshapenKill (kill headline : Name)
  | unmentionedHole (hole : Name)
  | challengeImport (dependency : ImportLine) (role? : Option Role)
  | filled (name : Name)
  | terminatesNotHole (headline definition : Name)
  | terminatesWithoutKill (headline definition : Name)
  | terminatesUnmentioned (headline definition : Name)
  | unnamedHypothesis (headline : Name) (hypothesis : String)
  | privateAuxiliary (headline auxiliary : Name)
  | codeInClosure (module : Name)
  | witnessMissing (headline : Name)
  | witnessPredeclared (witness headline : Name)
  | unplainName (name : Name)
  | challengeLookup (candidates : Array SourceFact)
  | challengeAbsent (module : Name) (file : String)
  | challengeFails (file : String)
  | solutionModule (found : Array Name)
  | importsChallenge (importing : ImportLine)
  | noStatementTarget
  | lock (violation : Lock.Violation) (owned? : Option OwnedFile)
  | lockUnreadable (problem : String)
  deriving BEq, Repr, Inhabited

structure Writes where
  lock? : Option (Array Lock.Entry)
  config? : Option Config
  deriving BEq, Repr, Inhabited

structure Result where
  errors : Array Error
  writes : Writes
  killSearch : Array Name
  deriving BEq, Repr, Inhabited

end Statement

end SoftwareChallenge

module

public import SoftwareChallenge.CoreCode.Rules.Standing
public import SoftwareChallenge.CoreCode.Rules.Statement

public section

namespace SoftwareChallenge

open Lean

namespace Lint

inductive Error where
  | violation (violation : Violation)
  | axiomUse (blame : AxiomBlame)
  | holeOutsideCode (hole module : Name)
  | mainOutsideProgram (module : Name)
  | notFixpoint (hole headline : Name)
  | claimOutsideWorldSpec (claim module : Name)
  | unregisteredClaim (registration : RegistrationFact)
  | lintWarning (lint : LintFact)
  | lock (violation : Lock.Violation) (owned? : Option OwnedFile)
  | lockMissing
  | lockUnreadable (problem : String)
  | comparatorMissing
  | comparatorStale (listedNotDeclared declaredNotListed : Array Name) (solutionListed? solutionExpected? : Option Name)
  | comparatorUnreadable (problem : String)
  | noStatementTarget
  | solutionModule (found : Array Name)
  | importsChallenge (importing : ImportLine)
  | builtinLintOn (place : Place)
  | proofUnreadable (target module : Name)
  deriving BEq, Repr, Inhabited

inductive Pending where
  | standing (target : Name) (standing : Standing)
  | mainMissing
  | unreachedHole (hole : Name)
  | undecidedCheck (use : ClaimUse) (check : CheckFact)
  | uncheckedClaim (use : ClaimUse)
  | hiddenDependency (dependency : PackageFact)
  deriving BEq, Repr, Inhabited

structure Result where
  errors : Array Error
  pending : Array Pending
  report : Array String
  code : UInt32
  deriving BEq, Repr, Inhabited

end Lint

end SoftwareChallenge

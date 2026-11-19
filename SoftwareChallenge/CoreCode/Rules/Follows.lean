module

public import SoftwareChallenge.CoreCode.Facts
public import SoftwareChallenge.CoreCode.Graph

public section

namespace SoftwareChallenge

open Lean

namespace Lint

def callGraph (solution : SolutionFacts) : Graph := .ofEdges solution.calls

def reachedFromMain (solution : SolutionFacts) : Std.HashSet Name :=
  let calls := callGraph solution
  calls.closure (calls.next `main)

def unreachedHoles (solution : SolutionFacts) (holes : Array Name) : Array Name :=
  holes.filter (!(reachedFromMain solution).contains ·)

def proofGraph (solution : SolutionFacts) : Graph := .ofEdges solution.proofUses

def followsFrom (proofs : Graph) (proved : Array Name) (headline : Name) : Array Name :=
  let others := proved.filter (· != headline)
  let graph := proofs.cut others
  let reached := graph.closure (graph.next headline)
  others.filter reached.contains

structure Assumed where
  claim : Name
  statement : String
  binders : Array Nat
  deriving BEq, Repr, Inhabited

def distinctStatements (claims : Array (Nat × Name × String)) : Array String :=
  claims.foldl (init := #[]) fun kept (_, _, statement) => if kept.contains statement then kept else kept.push statement

def assumed (headline : HeadlineFact) : Array Assumed :=
  (distinctStatements headline.claims).map fun statement =>
    let merged := headline.claims.filter (·.2.2 == statement)
    { claim := ((merged[0]?).map (·.2.1)).getD .anonymous, statement, binders := merged.map (·.1) }

def premisesOf? (solution : SolutionFacts) (headline : Name) : Option (Array Nat) :=
  (solution.premiseUses.find? (·.1 == headline)).map (·.2)

def unusedByProof (solution : SolutionFacts) (proved : Bool) (headline : Name) (binders : Array Nat) : Bool :=
  proved && (premisesOf? solution headline).any fun used => binders.all (!used.contains ·)

def importGraph (modules : Array ModuleFact) : Graph :=
  .ofEdges (modules.map fun fact => (fact.name, fact.imports.map (·.name)))

def solutionClosure (modules : Array ModuleFact) (solution : Name) : Std.HashSet Name :=
  (importGraph modules).closure #[solution]

def importingSolution (modules : Array ModuleFact) (solution : Name) : Array Name :=
  let importers := (importGraph modules).dependingOn #[solution]
  (modules.map (·.name)).filter fun module => module != solution && importers.contains module

end Lint

end SoftwareChallenge

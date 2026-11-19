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

def importGraph (modules : Array ModuleFact) : Graph :=
  .ofEdges (modules.map fun fact => (fact.name, fact.imports.map (·.name)))

def solutionClosure (modules : Array ModuleFact) (solution : Name) : Std.HashSet Name :=
  (importGraph modules).closure #[solution]

def importingSolution (modules : Array ModuleFact) (solution : Name) : Array Name :=
  let importers := (importGraph modules).dependingOn #[solution]
  (modules.map (·.name)).filter fun module => module != solution && importers.contains module

end Lint

end SoftwareChallenge

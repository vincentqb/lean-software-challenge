module

public import Std.Data.HashMap.Basic
public import Std.Data.HashSet.Basic

@[expose] public section

namespace SoftwareChallenge

open Lean

structure Graph where
  edges : Std.HashMap Name (Array Name)

def Graph.next (graph : Graph) (node : Name) : Array Name := graph.edges.getD node #[]

inductive Graph.Reaches (graph : Graph) : Name → Name → Prop where
  | refl (node : Name) : Reaches graph node node
  | step {source middle target : Name} :
      Reaches graph source middle → target ∈ graph.next middle → Reaches graph source target

end SoftwareChallenge

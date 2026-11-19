module

public import SoftwareChallenge.CoreCode.Graph
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

namespace SoftwareChallenge

open Lean

theorem Graph.closure_sound (graph : Graph) (roots : Array Name) (node : Name)
    (member : node ∈ graph.closure roots) : ∃ root ∈ roots, graph.Reaches root node :=
  Graph.mem_closure_iff.mp member

theorem Graph.closure_sound_rejects_extra_node :
    ¬ ∀ (graph : Graph) (roots : Array Name) (node : Name),
      node ∈ (fun (_ : Graph) (roots : Array Name) => Std.HashSet.ofList (roots.push `extra).toList) graph roots →
      ∃ root ∈ roots, graph.Reaches root node := by
  intro sound
  obtain ⟨_, rooted, _⟩ := sound ⟨∅⟩ #[] `extra (by simp)
  simp at rooted

theorem Graph.closure_sound_applies :
    ∃ (graph : Graph) (roots : Array Name) (node : Name), node ∈ graph.closure roots :=
  ⟨⟨∅⟩, #[`root], `root, Graph.mem_closure_iff.mpr ⟨`root, by simp, .refl `root⟩⟩

theorem Graph.closure_complete (graph : Graph) (roots : Array Name) (root node : Name) (rooted : root ∈ roots)
    (path : graph.Reaches root node) : node ∈ graph.closure roots :=
  Graph.mem_closure_iff.mpr ⟨root, rooted, path⟩

theorem Graph.closure_complete_rejects_roots_only :
    ¬ ∀ (graph : Graph) (roots : Array Name) (root node : Name), root ∈ roots → graph.Reaches root node →
      node ∈ (fun (_ : Graph) (roots : Array Name) => Std.HashSet.ofList roots.toList) graph roots := by
  intro complete
  have reached := complete ⟨(∅ : Std.HashMap Name (Array Name)).insert `a #[`b]⟩ #[`a] `a `b (by simp)
    (.step (.refl `a) (by simp [Graph.next]))
  simp at reached

end SoftwareChallenge

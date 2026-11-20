module

public import SoftwareChallenge.CoreSpec.Graph
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

namespace SoftwareChallenge

open Lean

namespace Graph

private def connect (map : Std.HashMap Name (Array Name)) (edge : Name × Array Name) :
    Std.HashMap Name (Array Name) :=
  map.alter edge.1 fun targets => some (targets.getD #[] ++ edge.2)

def ofEdges (edges : Array (Name × Array Name)) : Graph where
  edges := edges.foldl connect {}

def reverse (graph : Graph) : Graph :=
  ofEdges <| graph.edges.toArray.flatMap fun edge => edge.2.map (·, #[edge.1])

def cut (graph : Graph) (sinks : Array Name) : Graph where
  edges := sinks.foldl Std.HashMap.erase graph.edges

private def visit (graph : Graph) : Nat → List Name → Std.HashSet Name → Option (Std.HashSet Name)
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, node :: pending, seen =>
    if seen.contains node then visit graph fuel pending seen
    else visit graph fuel ((graph.next node).toList ++ pending) (seen.insert node)

private def budget (graph : Graph) (roots : Array Name) : Nat :=
  graph.edges.fold (fun total _ targets => total + targets.size) roots.size

def closure (graph : Graph) (roots : Array Name) : Std.HashSet Name :=
  (visit graph (budget graph roots) roots.toList {}).getD {}

def dependingOn (graph : Graph) (targets : Array Name) : Std.HashSet Name :=
  graph.reverse.closure targets

private def unexplored (seen : Std.HashSet Name) : List (Name × Array Name) → Nat
  | [] => 0
  | (node, targets) :: rest => (if seen.contains node then 0 else targets.size) + unexplored seen rest

private theorem entry_insert_le (seen : Std.HashSet Name) (node key : Name) (size : Nat) :
    (if (seen.insert node).contains key then 0 else size) ≤ (if seen.contains key then 0 else size) := by
  rw [Std.HashSet.contains_insert]
  cases seen.contains key
  · split <;> simp
  · simp

private theorem unexplored_insert_le (seen : Std.HashSet Name) (node : Name) :
    ∀ entries, unexplored (seen.insert node) entries ≤ unexplored seen entries
  | [] => Nat.le_refl 0
  | (key, targets) :: rest => by
    have later := unexplored_insert_le seen node rest
    have first := entry_insert_le seen node key targets.size
    simp only [unexplored]
    omega

private theorem unexplored_insert_add (seen : Std.HashSet Name) (node : Name) (targets : Array Name)
    (fresh : seen.contains node = false) :
    ∀ entries, (node, targets) ∈ entries → targets.size + unexplored (seen.insert node) entries ≤ unexplored seen entries
  | [], listed => absurd listed List.not_mem_nil
  | (key, found) :: rest, listed => by
    simp only [unexplored]
    rcases List.mem_cons.mp listed with same | later
    · obtain ⟨same_key, same_found⟩ := Prod.mk.inj same
      rw [← same_key, ← same_found]
      have rest_le := unexplored_insert_le seen node rest
      simp [fresh]
      omega
    · have rest_le := unexplored_insert_add seen node targets fresh rest later
      have first := entry_insert_le seen node key found.size
      omega

private theorem visit_isSome (graph : Graph) (fuel : Nat) (pending : List Name) (seen : Std.HashSet Name)
    (enough : pending.length + unexplored seen graph.edges.toList ≤ fuel) : (visit graph fuel pending seen).isSome := by
  fun_induction visit graph fuel pending seen with
  | case1 => rfl
  | case2 => simp at enough
  | case3 _ _ _ _ _ ih => exact ih (by simp at enough; omega)
  | case4 _ node _ seen fresh ih =>
    have explored : (graph.next node).size + unexplored (seen.insert node) graph.edges.toList ≤
        unexplored seen graph.edges.toList := by
      by_cases present : node ∈ graph.edges
      · exact unexplored_insert_add seen node _ (by simpa using fresh) _
          (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr (Std.HashMap.getElem?_eq_some_getD present))
      · simpa [Graph.next, Std.HashMap.getD_eq_fallback present] using unexplored_insert_le seen node _
    apply ih
    simp only [List.length_append, Array.length_toList, List.length_cons] at enough ⊢
    omega

private theorem foldl_size_eq_unexplored : ∀ (entries : List (Name × Array Name)) (total : Nat),
    entries.foldl (fun total entry => total + entry.2.size) total = total + unexplored {} entries
  | [], _ => rfl
  | (node, targets) :: rest, total => by
    simp only [List.foldl_cons, unexplored, Std.HashSet.contains_empty, Bool.false_eq_true, ↓reduceIte]
    rw [foldl_size_eq_unexplored rest]
    omega

private theorem budget_suffices (graph : Graph) (roots : Array Name) :
    (visit graph (budget graph roots) roots.toList {}).isSome :=
  visit_isSome graph _ _ _ (by
    simp only [budget, Std.HashMap.fold_eq_foldl_toList, foldl_size_eq_unexplored, Array.length_toList]
    omega)

private theorem visit_budget (graph : Graph) (roots : Array Name) :
    visit graph (budget graph roots) roots.toList {} = some (graph.closure roots) := by
  obtain ⟨reached, finished⟩ := Option.isSome_iff_exists.mp (budget_suffices graph roots)
  simp [closure, finished]

private theorem visit_sound {graph : Graph} {invariant : Name → Prop}
    (closed : ∀ source target, invariant source → target ∈ graph.next source → invariant target)
    {fuel : Nat} {pending : List Name} {seen reached : Std.HashSet Name}
    (finished : visit graph fuel pending seen = some reached) (known : ∀ y ∈ seen, invariant y)
    (waiting : ∀ y ∈ pending, invariant y) : ∀ y ∈ reached, invariant y := by
  fun_induction visit graph fuel pending seen with
  | case1 => cases finished; exact known
  | case2 => cases finished
  | case3 _ _ _ _ _ ih => exact ih finished known fun y listed => waiting y (List.mem_cons_of_mem _ listed)
  | case4 _ node _ _ _ ih =>
    refine ih finished (fun y member => ?_) (fun y listed => ?_)
    · rcases Std.HashSet.mem_insert.mp member with same | member
      · rw [← beq_iff_eq.mp same]; exact waiting node List.mem_cons_self
      · exact known y member
    · rcases List.mem_append.mp listed with next | later
      · exact closed node y (waiting node List.mem_cons_self) (Array.mem_toList_iff.mp next)
      · exact waiting y (List.mem_cons_of_mem _ later)

private theorem visit_complete {graph : Graph} {fuel : Nat} {pending : List Name} {seen reached : Std.HashSet Name}
    (finished : visit graph fuel pending seen = some reached)
    (closed : ∀ y ∈ seen, ∀ z ∈ graph.next y, z ∈ seen ∨ z ∈ pending) :
    (∀ y ∈ seen, y ∈ reached) ∧ (∀ y ∈ pending, y ∈ reached) ∧ ∀ y ∈ reached, ∀ z ∈ graph.next y, z ∈ reached := by
  fun_induction visit graph fuel pending seen with
  | case1 =>
    cases finished
    exact ⟨fun _ member => member, by simp, fun y member z edge => (closed y member z edge).resolve_right (by simp)⟩
  | case2 => cases finished
  | case3 _ node _ seen known ih =>
    have present : node ∈ seen := Std.HashSet.mem_iff_contains.mpr known
    obtain ⟨kept, waiting, shut⟩ := ih finished fun y member z edge => by
      rcases closed y member z edge with old | listed
      · exact .inl old
      · rcases List.mem_cons.mp listed with same | later
        · exact .inl (same ▸ present)
        · exact .inr later
    refine ⟨kept, fun y listed => ?_, shut⟩
    rcases List.mem_cons.mp listed with same | later
    · exact same ▸ kept node present
    · exact waiting y later
  | case4 _ node _ _ _ ih =>
    obtain ⟨kept, waiting, shut⟩ := ih finished fun y member z edge => by
      rcases Std.HashSet.mem_insert.mp member with same | member
      · rw [← beq_iff_eq.mp same] at edge
        exact .inr (List.mem_append.mpr (.inl (Array.mem_toList_iff.mpr edge)))
      · rcases closed y member z edge with old | listed
        · exact .inl (Std.HashSet.mem_insert.mpr (.inr old))
        · rcases List.mem_cons.mp listed with same | later
          · exact .inl (Std.HashSet.mem_insert.mpr (.inl (beq_iff_eq.mpr same.symm)))
          · exact .inr (List.mem_append.mpr (.inr later))
    refine ⟨fun y member => kept y (Std.HashSet.mem_insert.mpr (.inr member)), fun y listed => ?_, shut⟩
    rcases List.mem_cons.mp listed with same | later
    · exact same ▸ kept node (Std.HashSet.mem_insert.mpr (.inl BEq.rfl))
    · exact waiting y (List.mem_append.mpr (.inr later))

theorem mem_closure_iff {graph : Graph} {roots : Array Name} {node : Name} :
    node ∈ graph.closure roots ↔ ∃ root ∈ roots, graph.Reaches root node := by
  constructor
  · intro member
    exact visit_sound (invariant := fun node => ∃ root ∈ roots, graph.Reaches root node)
      (fun _ _ ⟨root, rooted, path⟩ edge => ⟨root, rooted, .step path edge⟩) (visit_budget graph roots)
      (by simp) (fun node listed => ⟨node, Array.mem_toList_iff.mp listed, .refl node⟩) node member
  · rintro ⟨root, rooted, path⟩
    obtain ⟨_, initial, closed⟩ := visit_complete (visit_budget graph roots) (by simp)
    induction path with
    | refl => exact initial _ (Array.mem_toList_iff.mpr rooted)
    | step _ edge reached => exact closed _ reached _ edge

private theorem mem_foldl_connect (source target : Name) :
    ∀ (edges : List (Name × Array Name)) (map : Std.HashMap Name (Array Name)),
      target ∈ (edges.foldl connect map).getD source #[] ↔
        target ∈ map.getD source #[] ∨ ∃ targets, (source, targets) ∈ edges ∧ target ∈ targets
  | [], _ => by simp
  | (key, targets) :: rest, map => by
    rw [List.foldl_cons, mem_foldl_connect source target rest]
    by_cases same : key = source
    · subst same
      simp only [connect, Std.HashMap.getD_alter_self, Option.getD_some, ← Std.HashMap.getD_eq_getD_getElem?,
        Array.mem_append, List.mem_cons, Prod.mk.injEq, true_and]
      constructor
      · rintro ((old | added) | ⟨found, listed, member⟩)
        · exact .inl old
        · exact .inr ⟨targets, .inl rfl, added⟩
        · exact .inr ⟨found, .inr listed, member⟩
      · rintro (old | ⟨found, rfl | listed, member⟩)
        · exact .inl (.inl old)
        · exact .inl (.inr member)
        · exact .inr ⟨found, listed, member⟩
    · simp [connect, Std.HashMap.getD_alter, same, Ne.symm same]

theorem mem_next_ofEdges {edges : Array (Name × Array Name)} {source target : Name} :
    target ∈ (ofEdges edges).next source ↔ ∃ targets, (source, targets) ∈ edges ∧ target ∈ targets := by
  simp only [ofEdges, Graph.next, ← Array.foldl_toList, mem_foldl_connect, Std.HashMap.getD_empty,
    Array.mem_toList_iff]
  simp

end Graph

end SoftwareChallenge

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Order.Monotone.Basic

/-!
# A finite breadth-first connectivity algorithm with a correctness proof

The naive decidability instance enumerates walks.  Here the accumulated vertex
set is stored at each step.  The result is proved equivalent to graph
reachability before it is used in any finite percolation computation.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : _root_.SimpleGraph V) [DecidableRel G.Adj]

def reachableBall (root : V) : ℕ → Finset V
  | 0 => {root}
  | n + 1 =>
      let previous := reachableBall root n
      previous ∪ previous.biUnion (fun v => G.neighborFinset v)

theorem reachableBall_mono (root : V) : Monotone (G.reachableBall root) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

theorem reachable_of_mem_reachableBall (root : V) (n : ℕ) {v : V}
    (h : v ∈ G.reachableBall root n) : G.Reachable root v := by
  induction n generalizing v with
  | zero =>
      have hv : v = root := by simpa [reachableBall] using h
      subst v
      exact .refl root
  | succ n ih =>
      rcases Finset.mem_union.mp h with h | h
      · exact ih h
      · rcases Finset.mem_biUnion.mp h with ⟨w, hw, hv⟩
        exact (ih hw).trans ((G.mem_neighborFinset w v).mp hv).reachable

theorem walk_start_mem_reachableBall {u v : V} (p : G.Walk u v) :
    u ∈ G.reachableBall v p.length := by
  induction p with
  | nil => simp [reachableBall]
  | @cons u w v h p ih =>
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      exact ⟨w, ih, (G.mem_neighborFinset w u).mpr h.symm⟩

theorem mem_reachableBall_card_iff (root v : V) :
    v ∈ G.reachableBall root (Fintype.card V) ↔ G.Reachable root v := by
  constructor
  · exact G.reachable_of_mem_reachableBall root _
  · intro h
    obtain ⟨p, hp⟩ := h.exists_isPath
    apply G.reachableBall_mono root (Nat.le_of_lt hp.length_lt)
    simpa only [_root_.SimpleGraph.Walk.length_reverse] using
      G.walk_start_mem_reachableBall p.reverse

def reachableDecide (root v : V) : Bool :=
  decide (v ∈ G.reachableBall root (Fintype.card V))

theorem reachableDecide_eq_true (root v : V) :
    G.reachableDecide root v = true ↔ G.Reachable root v := by
  simp only [reachableDecide, decide_eq_true_eq, G.mem_reachableBall_card_iff]

end SimpleGraph

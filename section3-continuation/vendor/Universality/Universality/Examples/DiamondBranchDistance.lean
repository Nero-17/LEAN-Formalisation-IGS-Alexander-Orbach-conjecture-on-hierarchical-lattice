import Universality.Examples.DiamondRadiusGeometry
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- A two-terminal cut forces the exact distance between opposite sides
to be the shorter of the two routes through its terminals. -/
theorem terminal_cut_distance (label : Fin vertices → Bool)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hlocal : ∀ {u v}, R.fullGraph.Adj u v → u ≠ R.source → u ≠ R.target →
      v ≠ R.source → v ≠ R.target → label u = label v)
    (first second : Fin vertices) (hdifferent : label first ≠ label second) :
    R.fullGraph.dist first second =
      min (R.fullGraph.dist R.source first + R.fullGraph.dist R.source second)
        (R.fullGraph.dist first R.target + R.fullGraph.dist second R.target) := by
  have hgate {u v : Fin vertices} (walk : R.fullGraph.Walk u v) :
      label u ≠ label v → R.source ∈ walk.support ∨ R.target ∈ walk.support := by
    induction walk with
    | nil => exact fun h => (h rfl).elim
    | @cons u v w hadj walk ih =>
        intro hlabels
        by_cases hus : u = R.source
        · left; simp [SimpleGraph.Walk.support_cons, hus]
        by_cases hut : u = R.target
        · right; simp [SimpleGraph.Walk.support_cons, hut]
        by_cases hvs : v = R.source
        · left
          exact List.mem_cons_of_mem _ (hvs ▸ walk.start_mem_support)
        by_cases hvt : v = R.target
        · right
          exact List.mem_cons_of_mem _ (hvt ▸ walk.start_mem_support)
        have hstep := hlocal hadj hus hut hvs hvt
        rcases ih (fun heq => hlabels (hstep.trans heq)) with hs | ht
        · exact Or.inl (List.mem_cons_of_mem _ hs)
        · exact Or.inr (List.mem_cons_of_mem _ ht)
  have hsource := ((hconnected first).symm).dist_triangle_left second
  have htarget := ((hconnected first).symm.trans (hconnected R.target)).dist_triangle_left second
  rw [SimpleGraph.dist_comm (u := first) (v := R.source)] at hsource
  rw [SimpleGraph.dist_comm (u := R.target) (v := second)] at htarget
  apply Nat.le_antisymm (le_min hsource htarget)
  obtain ⟨shortest, hlength⟩ := ((hconnected first).symm.trans (hconnected second)).exists_walk_length_eq_dist
  have hthrough (gate : Fin vertices) (hmem : gate ∈ shortest.support) :
      R.fullGraph.dist first gate + R.fullGraph.dist gate second ≤ R.fullGraph.dist first second := by
    have hleft := SimpleGraph.dist_le (shortest.takeUntil gate hmem)
    have hright := SimpleGraph.dist_le (shortest.dropUntil gate hmem)
    have hsplit := congrArg SimpleGraph.Walk.length (shortest.take_spec hmem)
    rw [SimpleGraph.Walk.length_append, hlength] at hsplit
    omega
  rcases hgate shortest hdifferent with hs | ht
  · have hbound := hthrough R.source hs
    rw [SimpleGraph.dist_comm (u := first) (v := R.source)] at hbound
    exact (min_le_left _ _).trans hbound
  · have hbound := hthrough R.target ht
    rw [SimpleGraph.dist_comm (u := R.target) (v := second)] at hbound
    exact (min_le_right _ _).trans hbound

end
end Universality.FiniteNetwork

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {innerVertices innerEdges : ℕ} (S : FiniteNetwork innerVertices innerEdges)

def diamondSubstitutionBranch : diamondNetwork.SubstitutionVertex S → Bool
  | .inl vertex => decide (vertex = 3)
  | .inr (edge, _) => decide (2 ≤ edge.val)

def diamondBranch (vertex : Fin (Fintype.card (diamondNetwork.SubstitutionVertex S))) : Bool :=
  diamondSubstitutionBranch S ((Fintype.equivFin _).symm vertex)

theorem diamondSubstitutionBranch_cell (edge : Fin 4) (vertex : Fin innerVertices)
    (hsource : diamondNetwork.cellVertex S edge vertex ≠ Sum.inl diamondNetwork.source)
    (htarget : diamondNetwork.cellVertex S edge vertex ≠ Sum.inl diamondNetwork.target) :
    diamondSubstitutionBranch S (diamondNetwork.cellVertex S edge vertex) = decide (2 ≤ edge.val) := by
  by_cases hs : vertex = S.source
  · subst vertex
    rw [diamondNetwork.cellVertex_source] at hsource htarget ⊢
    fin_cases edge <;> simp_all [diamondNetwork, diamondSubstitutionBranch]
  · by_cases ht : vertex = S.target
    · subst vertex
      rw [diamondNetwork.cellVertex_target] at hsource htarget ⊢
      fin_cases edge <;> simp_all [diamondNetwork, diamondSubstitutionBranch]
    · simp only [cellVertex, dif_neg hs, dif_neg ht, diamondSubstitutionBranch]

theorem diamondBranch_adj {u v : Fin (Fintype.card (diamondNetwork.SubstitutionVertex S))}
    (hadj : (diamondNetwork.substitute S).fullGraph.Adj u v)
    (hus : u ≠ (diamondNetwork.substitute S).source)
    (hut : u ≠ (diamondNetwork.substitute S).target)
    (hvs : v ≠ (diamondNetwork.substitute S).source)
    (hvt : v ≠ (diamondNetwork.substitute S).target) :
    diamondBranch S u = diamondBranch S v := by
  obtain ⟨u, rfl⟩ := (Fintype.equivFin (diamondNetwork.SubstitutionVertex S)).surjective u
  obtain ⟨v, rfl⟩ := (Fintype.equivFin (diamondNetwork.SubstitutionVertex S)).surjective v
  have hraw : (diamondNetwork.substitutedGraph S (fun _ _ => true)).Adj u v :=
    (diamondNetwork.substitutionGraphIso S (fun _ _ => true)).map_rel_iff.mp hadj
  obtain ⟨_, edge, first, second, _, rfl, rfl⟩ := hraw
  have hfirstSource : diamondNetwork.cellVertex S edge first ≠ Sum.inl diamondNetwork.source :=
    fun heq => hus (congrArg (Fintype.equivFin _) heq)
  have hfirstTarget : diamondNetwork.cellVertex S edge first ≠ Sum.inl diamondNetwork.target :=
    fun heq => hut (congrArg (Fintype.equivFin _) heq)
  have hsecondSource : diamondNetwork.cellVertex S edge second ≠ Sum.inl diamondNetwork.source :=
    fun heq => hvs (congrArg (Fintype.equivFin _) heq)
  have hsecondTarget : diamondNetwork.cellVertex S edge second ≠ Sum.inl diamondNetwork.target :=
    fun heq => hvt (congrArg (Fintype.equivFin _) heq)
  simp only [diamondBranch, Equiv.symm_apply_apply]
  rw [diamondSubstitutionBranch_cell S edge first hfirstSource hfirstTarget,
    diamondSubstitutionBranch_cell S edge second hsecondSource hsecondTarget]

/-- Opposite parallel branches in the actual four-cell diamond
substitution can communicate only through the two outer terminals. -/
theorem diamond_substitution_branch_distance
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (first second : Fin (Fintype.card (diamondNetwork.SubstitutionVertex S)))
    (hdifferent : diamondBranch S first ≠ diamondBranch S second) :
    (diamondNetwork.substitute S).fullGraph.dist first second =
      min ((diamondNetwork.substitute S).fullGraph.dist (diamondNetwork.substitute S).source first +
        (diamondNetwork.substitute S).fullGraph.dist (diamondNetwork.substitute S).source second)
        ((diamondNetwork.substitute S).fullGraph.dist first (diamondNetwork.substitute S).target +
          (diamondNetwork.substitute S).fullGraph.dist second (diamondNetwork.substitute S).target) :=
  (diamondNetwork.substitute S).terminal_cut_distance (diamondBranch S)
    (diamondNetwork.substitute_all_vertices_connected S diamondRule_classical.connected hinner)
    (fun hadj hus hut hvs hvt => diamondBranch_adj S hadj hus hut hvs hvt) first second hdifferent

end
end Universality

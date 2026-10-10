import Universality.Graph.FiniteWalkBalls
import Mathlib.Order.Filter.AtTopBot.Finite

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter

theorem finite_set_in_stage (tower : NetworkTower) {vertices : Set tower.Vertex}
    (hfinite : vertices.Finite) :
    ∃ n, ∀ vertex ∈ vertices, ∃ inside, tower.vertex n inside = vertex := by
  classical
  induction vertices, hfinite using Set.Finite.induction_on with
  | empty => exact ⟨0, fun vertex hvertex => False.elim hvertex⟩
  | @insert vertex vertices hvertex hfinite ih =>
    obtain ⟨i, first, hfirst⟩ := DirectLimit.exists_eq_mk tower.vertexEmbedding vertex
    change vertex = tower.vertex i first at hfirst
    obtain ⟨j, hrest⟩ := ih
    refine ⟨max i j, ?_⟩
    intro other hother
    rcases hother with rfl | hother
    · refine ⟨tower.vertexMap i (max i j) (Nat.le_max_left _ _) first, ?_⟩
      rw [tower.vertex_map]
      exact hfirst.symm
    · obtain ⟨inside, hinside⟩ := hrest other hother
      exact ⟨tower.vertexMap j (max i j) (Nat.le_max_right _ _) inside,
        (tower.vertex_map j (max i j) (Nat.le_max_right _ _) inside).trans hinside⟩

theorem finite_set_in_every_later_stage (tower : NetworkTower) {vertices : Set tower.Vertex}
    (hfinite : vertices.Finite) :
    ∃ n, ∀ k, n ≤ k → ∀ vertex ∈ vertices, ∃ inside, tower.vertex k inside = vertex := by
  obtain ⟨n, hstage⟩ := tower.finite_set_in_stage hfinite
  refine ⟨n, fun k hnk vertex hvertex => ?_⟩
  obtain ⟨inside, hinside⟩ := hstage vertex hvertex
  exact ⟨tower.vertexMap n k hnk inside, (tower.vertex_map n k hnk inside).trans hinside⟩

/-- Every bounded actual rooted ball is carried by all sufficiently large
finite stages. This uses local finiteness, not a presumed local-limit law. -/
theorem boundedWalkBall_in_every_later_stage (tower : NetworkTower)
    (configuration : tower.Edge → Bool)
    (hfinite : ∀ vertex, ((tower.openGraph configuration).neighborSet vertex).Finite)
    (root : tower.Vertex) (radius : ℕ) :
    ∃ n, ∀ k, n ≤ k → ∀ vertex ∈ boundedWalkBall (tower.openGraph configuration) root radius,
      ∃ inside, tower.vertex k inside = vertex :=
  tower.finite_set_in_every_later_stage
    (boundedWalkBall_finite (tower.openGraph configuration) hfinite root radius)

/-- On any actual finite vertex set, all adjacencies of a fixed configuration
are simultaneously visible in every sufficiently late stage. -/
theorem finite_set_adjacency_stabilizes (tower : NetworkTower)
    (configuration : tower.Edge → Bool) {vertices : Set tower.Vertex}
    (hfinite : vertices.Finite) :
    ∀ᶠ n in atTop, ∀ (first last : Fin (tower.stage n).vertices),
      tower.vertex n first ∈ vertices → tower.vertex n last ∈ vertices →
      ((tower.openGraph configuration).Adj (tower.vertex n first) (tower.vertex n last) ↔
        ((tower.stage n).network.openGraph (tower.restrictConfiguration configuration n)).Adj first last) := by
  classical
  letI : Fintype vertices := hfinite.fintype
  have hpair (first last : vertices) : ∀ᶠ n in atTop,
      (tower.openGraph configuration).Adj first.val last.val →
      ∃ (insideFirst insideLast : Fin (tower.stage n).vertices),
        tower.vertex n insideFirst = first.val ∧ tower.vertex n insideLast = last.val ∧
        ((tower.stage n).network.openGraph (tower.restrictConfiguration configuration n)).Adj
          insideFirst insideLast := by
    by_cases hadj : (tower.openGraph configuration).Adj first.val last.val
    · obtain ⟨j, insideFirst, insideLast, hfirst, hlast, hstage⟩ :=
        tower.adjacency_from_stage configuration hadj
      filter_upwards [eventually_ge_atTop j] with n hjn
      intro _
      refine ⟨tower.vertexMap j n hjn insideFirst, tower.vertexMap j n hjn insideLast,
        (tower.vertex_map j n hjn insideFirst).trans hfirst.symm,
        (tower.vertex_map j n hjn insideLast).trans hlast.symm, ?_⟩
      exact (tower.stageMapHom configuration j n hjn).map_rel' hstage
    · exact Eventually.of_forall (fun _ hfalse => False.elim (hadj hfalse))
  have hall := eventually_all.mpr (fun first => eventually_all.mpr (fun last => hpair first last))
  filter_upwards [hall] with n hn
  intro first last hfirst hlast
  constructor
  · intro hadj
    obtain ⟨insideFirst, insideLast, heqFirst, heqLast, hstage⟩ :=
      hn ⟨tower.vertex n first, hfirst⟩ ⟨tower.vertex n last, hlast⟩ hadj
    have hfirstEq := tower.vertex_injective n heqFirst
    have hlastEq := tower.vertex_injective n heqLast
    subst insideFirst
    subst insideLast
    exact hstage
  · intro hadj
    exact (tower.stageOpenGraphHom configuration n).map_rel' hadj

end
end Universality.NetworkTower

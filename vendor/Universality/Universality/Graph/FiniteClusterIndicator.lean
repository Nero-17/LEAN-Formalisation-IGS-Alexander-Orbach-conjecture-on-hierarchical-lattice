import Universality.Graph.FiniteClusterEvent

namespace Universality
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology

/-- A monotone family of finite clusters has eventually constant size-k
indicators, including when the union is infinite. -/
theorem finiteUnionHasSize_eventually_iff {α : Type*} (clusters : ℕ → Finset α)
    (hmono : Monotone clusters) (size : ℕ) :
    ∀ᶠ n in atTop, (clusters n).card = size ↔ finiteUnionHasSize clusters size := by
  classical
  by_cases hevent : finiteUnionHasSize clusters size
  · obtain ⟨first, hfirst⟩ := (finiteUnionHasSize_iff_eventually_card clusters hmono size).mp hevent
    exact eventually_atTop.mpr ⟨first, fun n hn => by simp only [hfirst n hn, hevent]⟩
  · by_cases hhit : ∃ n, (clusters n).card = size
    · obtain ⟨first, hfirst⟩ := hhit
      have hnot : ¬ ∀ n, first ≤ n → (clusters n).card = size := by
        intro h
        exact hevent ((finiteUnionHasSize_iff_eventually_card clusters hmono size).mpr ⟨first, h⟩)
      push Not at hnot
      obtain ⟨later, hlater, hne⟩ := hnot
      have hstrict : size < (clusters later).card := lt_of_le_of_ne
        (by rw [← hfirst]; exact Finset.card_le_card (hmono hlater)) (Ne.symm hne)
      refine eventually_atTop.mpr ⟨later, fun n hn => ?_⟩
      have hne' : (clusters n).card ≠ size :=
        (hstrict.trans_le (Finset.card_le_card (hmono hn))).ne'
      simp only [hne', hevent]
    · apply Eventually.of_forall
      intro n
      have hne : (clusters n).card ≠ size := fun heq => hhit ⟨n, heq⟩
      simp only [hne, hevent]

namespace NetworkTower
set_option backward.isDefEq.respectTransparency false

theorem exists_finiteClusterSizeEvent_iff_finite (tower : NetworkTower)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) :
    (∃ size, tower.finiteClusterSizeEvent configuration root size) ↔
      Set.Finite {vertex | (tower.openGraph configuration).Reachable (tower.vertex 0 root) vertex} := by
  classical
  constructor
  · rintro ⟨size, vertices, hvertices, hsize⟩
    have heq : (↑vertices : Set tower.Vertex) =
        {vertex | (tower.openGraph configuration).Reachable (tower.vertex 0 root) vertex} := by
      ext vertex
      exact hvertices vertex
    exact heq ▸ vertices.finite_toSet
  · intro hfinite
    refine ⟨hfinite.toFinset.card, hfinite.toFinset, ?_, rfl⟩
    intro vertex
    exact hfinite.mem_toFinset

/-- The residual event is genuinely an infinite connected component. -/
theorem no_finiteClusterSizeEvent_iff_infinite (tower : NetworkTower)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) :
    (¬ ∃ size, tower.finiteClusterSizeEvent configuration root size) ↔
      Set.Infinite {vertex | (tower.openGraph configuration).Reachable (tower.vertex 0 root) vertex} :=
  not_congr (tower.exists_finiteClusterSizeEvent_iff_finite configuration root)

theorem finiteClusterSizeEvent_unique (tower : NetworkTower)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices)
    {first second : ℕ} (hfirst : tower.finiteClusterSizeEvent configuration root first)
    (hsecond : tower.finiteClusterSizeEvent configuration root second) : first = second := by
  classical
  obtain ⟨vertices, hvertices, hfirst⟩ := hfirst
  obtain ⟨other, hother, hsecond⟩ := hsecond
  have heq : vertices = other := by
    ext vertex
    exact (hvertices vertex).trans (hother vertex).symm
  exact hfirst.symm.trans ((congrArg Finset.card heq).trans hsecond)

theorem finiteClusterSizeEvent_eventually_iff (tower : NetworkTower)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) (size : ℕ) :
    ∀ᶠ n in atTop,
      ((tower.stage n).network.clusterVertices (tower.restrictConfiguration configuration n)
        (tower.vertexMap 0 n (Nat.zero_le n) root)).card = size ↔
          tower.finiteClusterSizeEvent configuration root size := by
  have hevent : finiteUnionHasSize (tower.rootClusterStage configuration root) size ↔
      tower.finiteClusterSizeEvent configuration root size := by
    rw [finiteUnionHasSize_iff_eventually_card _
      (tower.rootClusterStage_monotone configuration root),
      tower.finiteClusterSizeEvent_iff_eventually_card]
    simp only [tower.rootClusterStage_card]
  filter_upwards [finiteUnionHasSize_eventually_iff (tower.rootClusterStage configuration root)
    (tower.rootClusterStage_monotone configuration root) size] with n hn
  rw [← tower.rootClusterStage_card configuration root n]
  exact hn.trans hevent

theorem finite_cluster_size_indicator_tendsto (tower : NetworkTower)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) (size : ℕ) :
    Tendsto (fun n => if ((tower.stage n).network.clusterVertices
      (tower.restrictConfiguration configuration n) (tower.vertexMap 0 n (Nat.zero_le n) root)).card = size
        then (1 : ℝ) else 0) atTop
      (𝓝 (if tower.finiteClusterSizeEvent configuration root size then 1 else 0)) := by
  classical
  have heq : (fun n => if ((tower.stage n).network.clusterVertices
      (tower.restrictConfiguration configuration n) (tower.vertexMap 0 n (Nat.zero_le n) root)).card = size
        then (1 : ℝ) else 0) =ᶠ[atTop]
      (fun _ => if tower.finiteClusterSizeEvent configuration root size then 1 else 0) := by
    filter_upwards [tower.finiteClusterSizeEvent_eventually_iff configuration root size] with n hn
    simp only [hn]
  exact tendsto_const_nhds.congr' heq.symm

end NetworkTower
end
end Universality

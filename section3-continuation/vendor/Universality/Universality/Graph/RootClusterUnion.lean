import Universality.Graph.StageReachability
import Universality.Percolation.FiniteClusters

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

def rootClusterStage (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (n : ℕ) : Finset tower.Vertex :=
  ((tower.stage n).network.clusterVertices (tower.restrictConfiguration configuration n)
    (tower.vertexMap 0 n (Nat.zero_le n) root)).map ⟨tower.vertex n, tower.vertex_injective n⟩

theorem mem_rootClusterStage (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (n : ℕ) (x : tower.Vertex) :
    x ∈ tower.rootClusterStage configuration root n ↔
      ∃ v : Fin (tower.stage n).vertices, x = tower.vertex n v ∧
        ((tower.stage n).network.openGraph (tower.restrictConfiguration configuration n)).Reachable
          (tower.vertexMap 0 n (Nat.zero_le n) root) v := by
  constructor
  · intro h
    obtain ⟨v, hv, heq⟩ := Finset.mem_map.mp h
    exact ⟨v, heq.symm, ((tower.stage n).network.mem_clusterVertices _ _ _).mp hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact Finset.mem_map.mpr ⟨v, ((tower.stage n).network.mem_clusterVertices _ _ _).mpr hv, rfl⟩

theorem rootClusterStage_monotone (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) : Monotone (tower.rootClusterStage configuration root) := by
  intro i j hij x hx
  obtain ⟨v, hx, hreach⟩ := (tower.mem_rootClusterStage configuration root i x).mp hx
  apply (tower.mem_rootClusterStage configuration root j x).mpr
  refine ⟨tower.vertexMap i j hij v, hx.trans (tower.vertex_map i j hij v).symm, ?_⟩
  have hmapped : ((tower.stage j).network.openGraph
      (tower.restrictConfiguration configuration j)).Reachable
      (tower.vertexMap i j hij (tower.vertexMap 0 i (Nat.zero_le i) root))
      (tower.vertexMap i j hij v) := hreach.map (tower.stageMapHom configuration i j hij)
  have hroot : tower.vertexMap i j hij (tower.vertexMap 0 i (Nat.zero_le i) root) =
      tower.vertexMap 0 j (Nat.zero_le j) root :=
    DirectedSystem.map_map (f := fun i j hij => tower.vertexMap i j hij) (Nat.zero_le i) hij root
  rwa [hroot] at hmapped

theorem actual_root_cluster_eq_iUnion (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) :
    {x | (tower.openGraph configuration).Reachable (tower.vertex 0 root) x} =
      ⋃ n, (tower.rootClusterStage configuration root n : Set tower.Vertex) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe, tower.mem_rootClusterStage]
  exact tower.rooted_reachable_iff configuration root x

theorem rootClusterStage_card (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (n : ℕ) :
    (tower.rootClusterStage configuration root n).card =
      ((tower.stage n).network.clusterVertices (tower.restrictConfiguration configuration n)
        (tower.vertexMap 0 n (Nat.zero_le n) root)).card := Finset.card_map _

theorem rootClusterStage_card_monotone (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) :
    Monotone (fun n => (tower.rootClusterStage configuration root n).card) :=
  fun _ _ hij => Finset.card_le_card (tower.rootClusterStage_monotone configuration root hij)

end
end Universality.NetworkTower

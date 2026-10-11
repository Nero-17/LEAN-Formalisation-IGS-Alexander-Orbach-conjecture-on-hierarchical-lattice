import Universality.Graph.TowerRootedBallIsomorphism
import Universality.Graph.RootClusterUnion
import Universality.Percolation.ClusterRadius

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter

/-- The genuine ambient-distance radius tail of the actual open component. -/
def radiusTailEvent (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (radius : ℕ) : Prop :=
  ∃ vertex, (tower.openGraph configuration).Reachable (tower.vertex 0 root) vertex ∧
    radius ≤ (tower.openGraph (fun _ => true)).dist (tower.vertex 0 root) vertex

def stageRootClusterRadius (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (n : ℕ) : ℕ :=
  (tower.stage n).network.rootClusterRadius (tower.restrictConfiguration configuration n)
    (tower.vertexMap 0 n (Nat.zero_le n) root)

theorem stageRootClusterRadius_eq_sup (tower : NetworkTower) (hisometry : tower.IsometricSteps)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) (n : ℕ) :
    tower.stageRootClusterRadius configuration root n =
      (tower.rootClusterStage configuration root n).sup
        ((tower.openGraph (fun _ => true)).dist (tower.vertex 0 root)) := by
  unfold stageRootClusterRadius FiniteNetwork.rootClusterRadius FiniteNetwork.clusterRadius rootClusterStage
  rw [Finset.sup_map]
  apply Finset.sup_congr rfl
  intro vertex _
  exact (tower.fullGraph_root_distance hisometry hconnected root n vertex).symm

theorem stageRootClusterRadius_monotone (tower : NetworkTower) (hisometry : tower.IsometricSteps)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) :
    Monotone (tower.stageRootClusterRadius configuration root) := by
  intro i j hij
  rw [tower.stageRootClusterRadius_eq_sup hisometry hconnected,
    tower.stageRootClusterRadius_eq_sup hisometry hconnected]
  exact Finset.sup_mono (tower.rootClusterStage_monotone configuration root hij)

theorem radiusTailEvent_iff_exists_stage (tower : NetworkTower) (hisometry : tower.IsometricSteps)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) (radius : ℕ) :
    tower.radiusTailEvent configuration root radius ↔
      ∃ n, radius ≤ tower.stageRootClusterRadius configuration root n := by
  constructor
  · rintro ⟨vertex, hreach, hradius⟩
    obtain ⟨n, inside, rfl, hinside⟩ := (tower.rooted_reachable_iff configuration root vertex).mp hreach
    rw [tower.fullGraph_root_distance hisometry hconnected] at hradius
    refine ⟨n, hradius.trans ?_⟩
    exact (tower.stage n).network.dist_le_clusterRadius _ _ inside
      (((tower.stage n).network.mem_clusterVertices _ _ _).mpr hinside)
  · rintro ⟨n, hradius⟩
    have hnonempty : ((tower.stage n).network.clusterVertices
        (tower.restrictConfiguration configuration n) (tower.vertexMap 0 n (Nat.zero_le n) root)).Nonempty :=
      ⟨tower.vertexMap 0 n (Nat.zero_le n) root,
        ((tower.stage n).network.mem_clusterVertices _ _ _).mpr (.refl _)⟩
    obtain ⟨inside, hinside, hmax⟩ := Finset.exists_mem_eq_sup _ hnonempty
      ((tower.stage n).network.fullGraph.dist (tower.vertexMap 0 n (Nat.zero_le n) root))
    refine ⟨tower.vertex n inside,
      (tower.rooted_reachable_iff configuration root _).mpr
        ⟨n, inside, rfl, ((tower.stage n).network.mem_clusterVertices _ _ _).mp hinside⟩, ?_⟩
    rw [tower.fullGraph_root_distance hisometry hconnected]
    exact hradius.trans_eq hmax

theorem radiusTailEvent_stage_stabilizes (tower : NetworkTower) (hisometry : tower.IsometricSteps)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) (radius : ℕ) :
    ∀ᶠ n in atTop, (radius ≤ tower.stageRootClusterRadius configuration root n) ↔
      tower.radiusTailEvent configuration root radius := by
  classical
  by_cases hevent : tower.radiusTailEvent configuration root radius
  · obtain ⟨first, hfirst⟩ := (tower.radiusTailEvent_iff_exists_stage hisometry hconnected
      configuration root radius).mp hevent
    filter_upwards [eventually_ge_atTop first] with n hn
    exact ⟨fun _ => hevent, fun _ => hfirst.trans
      (tower.stageRootClusterRadius_monotone hisometry hconnected configuration root hn)⟩
  · exact Eventually.of_forall (fun n => ⟨fun hn => False.elim (hevent
      ((tower.radiusTailEvent_iff_exists_stage hisometry hconnected configuration root radius).mpr ⟨n, hn⟩)),
      fun hfalse => False.elim (hevent hfalse)⟩)

end
end Universality.NetworkTower

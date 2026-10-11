import Universality.Graph.TowerWalkLift
import Universality.Graph.CellIsometry

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

def IsometricSteps (tower : NetworkTower) : Prop :=
  ∀ (n : ℕ) (first last : Fin (tower.stage n).vertices),
    (tower.stage (n + 1)).network.fullGraph.dist
      ((tower.step n).vertex first) ((tower.step n).vertex last) =
        (tower.stage n).network.fullGraph.dist first last

theorem vertexMap_distance (tower : NetworkTower) (hisometry : tower.IsometricSteps)
    (i j : ℕ) (hij : i ≤ j) (first last : Fin (tower.stage i).vertices) :
    (tower.stage j).network.fullGraph.dist (tower.vertexMap i j hij first)
      (tower.vertexMap i j hij last) = (tower.stage i).network.fullGraph.dist first last := by
  induction j, hij using Nat.le_induction with
  | base => simp only [vertexMap, Nat.leRecOn_self]
  | succ j hij ih =>
    simp only [vertexMap, Nat.leRecOn_succ hij]
    rw [hisometry]
    exact ih

/-- No path appearing in the infinite graph can create a shortcut between
vertices of an isometrically embedded finite stage. -/
theorem fullGraph_distance (tower : NetworkTower) (hisometry : tower.IsometricSteps)
    (n : ℕ) (first last : Fin (tower.stage n).vertices)
    (hconnected : (tower.stage n).network.fullGraph.Reachable first last) :
    (tower.openGraph (fun _ => true)).dist (tower.vertex n first) (tower.vertex n last) =
      (tower.stage n).network.fullGraph.dist first last := by
  apply Nat.le_antisymm
  · obtain ⟨walk, hlength⟩ := hconnected.exists_walk_length_eq_dist
    have hbound := SimpleGraph.dist_le
      (walk.map (tower.stageOpenGraphHom (fun _ => true) n))
    change (tower.openGraph (fun _ => true)).dist (tower.vertex n first)
      (tower.vertex n last) ≤ (walk.map (tower.stageOpenGraphHom (fun _ => true) n)).length at hbound
    simpa only [SimpleGraph.Walk.length_map, hlength] using hbound
  · have hlimitConnected := hconnected.map (tower.stageOpenGraphHom (fun _ => true) n)
    obtain ⟨walk, hlength⟩ := hlimitConnected.exists_walk_length_eq_dist
    obtain ⟨k, hnk, lifted, hlifted⟩ :=
      tower.walk_from_stage_fixedEndpoints (fun _ => true) n first last walk
    calc
      (tower.stage n).network.fullGraph.dist first last =
          (tower.stage k).network.fullGraph.dist (tower.vertexMap n k hnk first)
            (tower.vertexMap n k hnk last) := (tower.vertexMap_distance hisometry n k hnk first last).symm
      _ ≤ lifted.length := SimpleGraph.dist_le lifted
      _ = (tower.openGraph (fun _ => true)).dist (tower.vertex n first) (tower.vertex n last) :=
        hlifted.trans hlength

theorem fullGraph_reachable (tower : NetworkTower)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (first last : tower.Vertex) : (tower.openGraph (fun _ => true)).Reachable first last := by
  obtain ⟨i, first, rfl⟩ := DirectLimit.exists_eq_mk tower.vertexEmbedding first
  obtain ⟨j, last, rfl⟩ := DirectLimit.exists_eq_mk tower.vertexEmbedding last
  let k := max i j
  have hi : i ≤ k := Nat.le_max_left _ _
  have hj : j ≤ k := Nat.le_max_right _ _
  have hstage := (hconnected k (tower.vertexMap i k hi first)).symm.trans
    (hconnected k (tower.vertexMap j k hj last))
  have hlimit := hstage.map (tower.stageOpenGraphHom (fun _ => true) k)
  change (tower.openGraph (fun _ => true)).Reachable
    (tower.vertex k (tower.vertexMap i k hi first))
    (tower.vertex k (tower.vertexMap j k hj last)) at hlimit
  change (tower.openGraph (fun _ => true)).Reachable (tower.vertex i first) (tower.vertex j last)
  simpa only [tower.vertex_map] using hlimit

end
end Universality.NetworkTower

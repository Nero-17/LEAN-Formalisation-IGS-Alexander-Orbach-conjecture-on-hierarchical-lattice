import Universality.Graph.TowerDistance
import Universality.Graph.ClassicalSubstitution

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

theorem Classical.generationCellEmbedding_distance {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (edge : Fin rule.edges)
    (first last : Fin (rule.generation depth).vertices) :
    (rule.generation (depth + 1)).network.fullGraph.dist
      ((rule.generationCellEmbedding depth edge).vertex first)
      ((rule.generationCellEmbedding depth edge).vertex last) =
        (rule.generation depth).network.fullGraph.dist first last := by
  have hcell := rule.network.substitute_cell_distance (rule.generation depth).network
    (h.generation depth).connected edge first last
  have hconnected := ((h.generation depth).connected first).symm.trans
    ((h.generation depth).connected last)
  have hmapped := hconnected.map
    ((rule.network.cellNetworkEmbedding (rule.generation depth).network edge).openGraphHom
      (fun _ => true))
  have hequiv := graph_iso_distance_of_reachable
    ((rule.generationTopDecomposition depth).symm.openGraphIso (fun _ => true)) hmapped
  exact hequiv.trans hcell

theorem Classical.ancestralTower_isometricSteps {rule : Rule} (h : rule.Classical)
    (age : ℕ) (address : ℕ → Fin rule.edges) :
    (rule.ancestralTower age address).IsometricSteps := by
  intro n first last
  exact h.generationCellEmbedding_distance (age + n) (address n) first last

theorem Classical.ancestralTower_fullGraph_distance {rule : Rule} (h : rule.Classical)
    (age : ℕ) (address : ℕ → Fin rule.edges) (n : ℕ)
    (first last : Fin (rule.generation (age + n)).vertices) :
    ((rule.ancestralTower age address).openGraph (fun _ => true)).dist
      ((rule.ancestralTower age address).vertex n first)
      ((rule.ancestralTower age address).vertex n last) =
        (rule.generation (age + n)).network.fullGraph.dist first last :=
  (rule.ancestralTower age address).fullGraph_distance
    (h.ancestralTower_isometricSteps age address) n first last
    (((h.generation (age + n)).connected first).symm.trans
      ((h.generation (age + n)).connected last))

end
end Universality.Rule

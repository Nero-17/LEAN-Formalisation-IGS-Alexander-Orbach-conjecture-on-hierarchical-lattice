import Universality.Graph.FrozenTowerNeighborhood
import Universality.Graph.GenerationInternalNeighborhood

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ancestralTower_preservesInterior (rule : Rule) (age : ℕ) (address : ℕ → Fin rule.edges) :
    (rule.ancestralTower age address).PreservesInterior := by
  intro n
  exact rule.generationCellEmbedding_internal (age + n) (address n)

theorem ancestralTower_noNewInteriorNeighbors (rule : Rule) (age : ℕ)
    (address : ℕ → Fin rule.edges) :
    (rule.ancestralTower age address).NoNewInteriorNeighbors := by
  intro n
  exact rule.generationCellEmbedding_internal_neighbor (age + n) (address n)

/-- An actual internal stage vertex has a finite neighborhood in the
direct-limit graph, for every ancestry and every edge configuration. -/
theorem ancestralTower_internal_finite_neighborSet (rule : Rule) (age : ℕ)
    (address : ℕ → Fin rule.edges)
    (configuration : (rule.ancestralTower age address).Edge → Bool)
    (n : ℕ) (vertex : (rule.generation (age + n)).network.InteriorVertex) :
    (((rule.ancestralTower age address).openGraph configuration).neighborSet
      ((rule.ancestralTower age address).vertex n vertex.val)).Finite :=
  (rule.ancestralTower age address).finite_neighborSet_of_internal
    (rule.ancestralTower_preservesInterior age address)
    (rule.ancestralTower_noNewInteriorNeighbors age address) configuration n vertex

theorem ancestralTower_finite_neighborSet_of_eventuallyInternal (rule : Rule) (age : ℕ)
    (address : ℕ → Fin rule.edges)
    (heventual : (rule.ancestralTower age address).EventuallyInternal)
    (configuration : (rule.ancestralTower age address).Edge → Bool)
    (vertex : (rule.ancestralTower age address).Vertex) :
    (((rule.ancestralTower age address).openGraph configuration).neighborSet vertex).Finite :=
  (rule.ancestralTower age address).finite_neighborSet_of_eventuallyInternal
    (rule.ancestralTower_preservesInterior age address)
    (rule.ancestralTower_noNewInteriorNeighbors age address) heventual configuration vertex

end
end Universality.Rule

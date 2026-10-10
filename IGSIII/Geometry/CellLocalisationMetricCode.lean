import IGSIII.Geometry.CellLocalisationLaw
import IGSIII.Geometry.OffsetSkeletonCompatibility

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution
open IGSIII.Probability MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem weightedDistance_congr_on_edges (graph : SimpleGraph Vertex) (first_cost last_cost : Sym2 Vertex → ℝ)
    (equal_costs : ∀ bond ∈ graph.edgeSet, first_cost bond = last_cost bond) (first last : Vertex) :
    weightedDistance graph first_cost first last = weightedDistance graph last_cost first last := by
  classical
  by_cases reachable : graph.Reachable first last
  · rw [weightedDistance_of_reachable graph _ reachable, weightedDistance_of_reachable graph _ reachable]
    apply shortest_congr_used
    intro path membership bond bond_member
    obtain ⟨walk, _, rfl⟩ := (mem_graphPathFamily graph first last reachable path).mp membership
    exact equal_costs bond (walk.edges_subset_edgeSet (List.mem_toFinset.mp bond_member))
  · simp only [weightedDistance, dif_neg reachable]

/-- Removing closed-edge lengths from the cost leaves every actual pair
metric unchanged. Thus the code is exactly the constructed critical skeleton
metric, including all of its retained interior vertices. -/
theorem chemicalMetricCode_root_distance (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p)
    (growth amplitude : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (first last : Fin (rule.generation depth).vertices) :
    (chemicalMetricCode rule p positive below_one fixed_point growth amplitude value marks).2 true depth first last =
      weightedDistance ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true))
        (indexedBondCost (rule.generation depth).network
          (chemicalBlockLimitLength rule p positive below_one fixed_point growth amplitude value marks depth)) first last := by
  change weightedDistance _ _ first last = _
  apply weightedDistance_congr_on_edges
  intro bond
  refine Sym2.inductionOn bond (fun left right => ?_)
  intro adjacent
  change ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Adj left right at adjacent
  obtain ⟨_, edge, opened, endpoints | endpoints⟩ := adjacent
  · have bond_identity : s(((rule.generation depth).network.endpoint edge).1,
        ((rule.generation depth).network.endpoint edge).2) = s(left, right) := by rw [endpoints]
    rw [← bond_identity, indexedBondCost_endpoint _ (classicalRule.generation depth).simple,
      indexedBondCost_endpoint _ (classicalRule.generation depth).simple]
    simp only [chemicalBlockLimitLength, opened, ↓reduceIte]
  · have bond_identity : s(((rule.generation depth).network.endpoint edge).1,
        ((rule.generation depth).network.endpoint edge).2) = s(left, right) := by rw [endpoints, Sym2.eq_swap]
    rw [← bond_identity, indexedBondCost_endpoint _ (classicalRule.generation depth).simple,
      indexedBondCost_endpoint _ (classicalRule.generation depth).simple]
    simp only [chemicalBlockLimitLength, opened, ↓reduceIte]

/-- The intrinsic cell metric is scaled by its actual global depth. -/
theorem chemicalMetricCode_scale (rule : Rule)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p)
    (growth amplitude factor : ℝ) (factor_nonnegative : 0 ≤ factor)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (opened : Bool) (depth : ℕ) (first last : Fin (rule.generation depth).vertices) :
    (chemicalMetricCode rule p positive below_one fixed_point growth (factor * amplitude) value marks).2 opened depth first last =
      factor * (chemicalMetricCode rule p positive below_one fixed_point growth amplitude value marks).2 opened depth first last := by
  change weightedDistance _ (indexedBondCost _ _) _ _ = factor * weightedDistance _ (indexedBondCost _ _) _ _
  have values_identity :
      (fun edge => factor * amplitude * chemicalField rule p positive below_one fixed_point value
        (generationEdgeAddress rule depth edge) marks / growth ^ (depth + 1)) =
      (fun edge => factor * (amplitude * chemicalField rule p positive below_one fixed_point value
        (generationEdgeAddress rule depth edge) marks / growth ^ (depth + 1))) := by
    funext edge
    ring
  rw [values_identity, indexedBondCost_scale, weightedDistance_scale _ _ factor factor_nonnegative]

theorem chemicalField_shift (rule : Rule)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive below_one fixed_point))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (first last : List (Fin rule.edges)) :
    chemicalField rule p positive below_one fixed_point value last (innovationTreeShift rule first marks) =
      chemicalField rule p positive below_one fixed_point value (first ++ last) marks := by
  exact congrArg value (innovationTreeShift_append rule first last marks)

end
end IGSIII.Geometry

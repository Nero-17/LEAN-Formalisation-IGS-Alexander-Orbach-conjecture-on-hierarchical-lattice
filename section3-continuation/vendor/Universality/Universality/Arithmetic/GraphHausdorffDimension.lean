import Universality.Geometry.GenerationHausdorffDimension
import Universality.Arithmetic.GraphCriticalDimensions

/-! Identify the ambient coordinate used by Section 4 arithmetic with the
Hausdorff dimension of the actual rescaled graph metric limit. The mass and
pivotal coordinates retain their established finite-expectation growth meaning. -/

namespace Universality.Rule
noncomputable section

/-- The ambient coordinate is an actual Hausdorff dimension, independently
of the value of the percolation parameter. -/
theorem Classical.criticalDimensions_ambient_hausdorff {rule : Rule} (h : rule.Classical)
    (p : ℝ) :
    dimH (Set.univ : Set (GenerationMetricSpace h)) = ENNReal.ofReal (rule.criticalDimensions p 0) := by
  exact generationMetricSpace_dimH_eq h

/-- The three coordinates simultaneously describe the actual compact ambient
space and the actual finite-generation mass and pivotal growth observables. -/
theorem Classical.criticalDimensions_geometric_finite_growth {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    (dimH (Set.univ : Set (GenerationMetricSpace h)) = ENNReal.ofReal (rule.criticalDimensions p 0)) ∧
    (∀ n : ℕ, Real.log ((rule.generation n).edges : ℝ) /
      Real.log ((rule.generation n).network.fullGraph.dist
        (rule.generation n).network.source (rule.generation n).network.target) =
      rule.criticalDimensions p 0) ∧
    (∀ state : FiniteNetwork.LiveState, Filter.Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalClusterMass p state) /
        Real.log ((rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source (rule.generation n).network.target))
      Filter.atTop (nhds (rule.criticalDimensions p 1))) ∧
    Filter.Tendsto (rule.pivotalLogarithmicGrowth p) Filter.atTop (nhds (rule.criticalDimensions p 2)) := by
  exact ⟨h.criticalDimensions_ambient_hausdorff p, h.criticalDimensions_finite_growth p hp hp' hfixed⟩

end
end Universality.Rule

#print axioms Universality.Rule.Classical.criticalDimensions_ambient_hausdorff
#print axioms Universality.Rule.Classical.criticalDimensions_geometric_finite_growth
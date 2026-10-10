import Universality.Percolation.FarConnectedPairs
import Universality.Graph.GenerationDiameter
import Universality.Percolation.BoundaryMassMoments

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

/-- At any fixed coarse depth, the expected number of connected pairs farther
apart than a child diameter grows at most like the squared critical mass. -/
theorem Classical.expected_far_pair_growth {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    {outerVertices outerEdges : ℕ} (outer : FiniteNetwork outerVertices outerEdges) :
    ∃ diameter : ℕ, 0 < diameter ∧ ∃ constant : ℝ, 0 < constant ∧ ∀ n : ℕ,
      (∑ configuration : Configuration (outerEdges * (rule.generation n).edges),
        bernoulliWeight p configuration *
          (((outer.substitute (rule.generation n).network).farConnectedPairs configuration
            (diameter * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n)).card : ℝ)) ≤
        constant * (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ (2 * n) := by
  obtain ⟨diameter, hdiameter, hdist⟩ := h.generation_diameter_bound
  obtain ⟨moment, hmoment, hbound⟩ := h.internal_boundary_moment_bounds p hp hp' hfixed 2
  let constant : ℝ := (outerVertices : ℝ) * ((outerEdges : ℝ) + 1) *
    ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) * moment)
  have hconstant : 0 ≤ constant := by dsimp [constant]; positivity
  refine ⟨diameter, hdiameter, constant + 1, by positivity, ?_⟩
  intro n
  have hradius : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed
        h.massAdmissible.symmetric h.scale).2.1
  have hscale : (1 : ℝ) ≤
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ (2 * n) :=
    one_le_pow₀ hradius.le
  have hbound' := mul_le_mul_of_nonneg_left (hbound n) (Nat.cast_nonneg outerEdges : (0 : ℝ) ≤ _)
  have hvertices := mul_le_mul_of_nonneg_left hscale (sq_nonneg (outerVertices : ℝ))
  have hsum : (outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) *
      (rule.generation n).network.expectedInternalBoundaryMoment p 2 ≤
      ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) * moment) *
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ (2 * n) := by
    nlinarith
  calc
    _ ≤ (outerVertices : ℝ) * ((outerEdges : ℝ) + 1) *
        ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) *
          (rule.generation n).network.expectedInternalBoundaryMoment p 2) :=
      outer.expected_farConnectedPairs_le_boundary_second_moment (rule.generation n).network
        (h.generation n).connected _ (hdist n) hp.le hp'.le
    _ ≤ constant * (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ (2 * n) := by
      simpa only [constant, mul_assoc] using
        mul_le_mul_of_nonneg_left hsum (show 0 ≤ (outerVertices : ℝ) * ((outerEdges : ℝ) + 1) by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (zero_le_one.trans hscale)

end
end Universality.Rule

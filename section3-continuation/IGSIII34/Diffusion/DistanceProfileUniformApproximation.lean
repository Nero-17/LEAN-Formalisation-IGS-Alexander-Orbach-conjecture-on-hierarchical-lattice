import IGSIII34.Diffusion.CountableDistanceProfile

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology

/-- Uniform convergence of each original distance-to-birth coordinate
implies uniform convergence of the entire fixed compact cube profile. -/
theorem distanceProfile_uniform_of_distance_uniform
    {Labels Target : Type*} [Countable Labels] [PseudoMetricSpace Target]
    (FiniteSpace : ℕ → Type*) [∀ depth, PseudoMetricSpace (FiniteSpace depth)]
    (finiteBirths : ∀ depth, Labels → FiniteSpace depth)
    (births : Labels → Target) (projection : ∀ depth, FiniteSpace depth → Target)
    (distanceClose : ∀ label tolerance, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |dist vertex (finiteBirths depth label) -
        dist (projection depth vertex) (births label)| < tolerance)
    (tolerance : ℝ) (positive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ vertex,
      dist (distanceProfilePoint (finiteBirths depth) vertex)
        (distanceProfilePoint births (projection depth vertex)) < tolerance := by
  apply countableDistanceProfile_uniform_of_coordinate_uniform FiniteSpace
    (fun depth => distanceProfilePoint (finiteBirths depth))
    (fun depth vertex => distanceProfilePoint births (projection depth vertex)) _ tolerance positive
  intro label coordinateTolerance coordinatePositive
  filter_upwards [distanceClose label coordinateTolerance coordinatePositive] with depth close
  intro vertex
  change |Real.exp (-dist vertex (finiteBirths depth label)) -
    Real.exp (-dist (projection depth vertex) (births label))| < coordinateTolerance
  exact (exp_neg_distance_difference_le dist_nonneg dist_nonneg).trans_lt (close vertex)

end
end IGSIII34.Diffusion

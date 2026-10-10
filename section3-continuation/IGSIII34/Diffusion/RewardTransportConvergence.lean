import IGSIII34.Diffusion.DegreeTransport

/-! Finite-frontier analytical assembly. Applying these lemmas to the actual
full clusters still requires the joint edge/vertex reward limits for every
inherited oriented component; those hypotheses are deliberately visible. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace IGSIII34.Diffusion
noncomputable section
open Universality MeasureTheory Filter
open scoped BigOperators Topology

theorem normalized_reward_ratio (numerator denominator : ℕ → ℝ)
    (growth numeratorLimit denominatorLimit : ℝ) (growthNonzero : growth ≠ 0)
    (denominatorNonzero : denominatorLimit ≠ 0)
    (numeratorConvergence : Tendsto (fun depth => numerator depth / growth ^ depth)
      atTop (𝓝 numeratorLimit))
    (denominatorConvergence : Tendsto (fun depth => denominator depth / growth ^ depth)
      atTop (𝓝 denominatorLimit)) :
    Tendsto (fun depth => numerator depth / denominator depth)
      atTop (𝓝 (numeratorLimit / denominatorLimit)) := by
  convert numeratorConvergence.div denominatorConvergence denominatorNonzero using 1
  ext depth
  dsimp only [Pi.div_apply]
  field_simp [growthNonzero]

theorem reward_constant_cancels (numerator denominator : ℕ → ℝ)
    (growth coefficient componentMass rootMass : ℝ) (growthNonzero : growth ≠ 0)
    (coefficientPositive : 0 < coefficient) (rootPositive : 0 < rootMass)
    (numeratorConvergence : Tendsto (fun depth => numerator depth / growth ^ depth)
      atTop (𝓝 (coefficient * componentMass)))
    (denominatorConvergence : Tendsto (fun depth => denominator depth / growth ^ depth)
      atTop (𝓝 (coefficient * rootMass))) :
    Tendsto (fun depth => numerator depth / denominator depth)
      atTop (𝓝 (componentMass / rootMass)) := by
  have result := normalized_reward_ratio numerator denominator growth
    (coefficient * componentMass) (coefficient * rootMass) growthNonzero
    (mul_pos coefficientPositive rootPositive).ne' numeratorConvergence denominatorConvergence
  simpa only [mul_div_mul_left _ _ coefficientPositive.ne'] using result

/-- The edge and first-birth vertex allocations have the same finite-anchor
limit whenever their proved rewards have the same component martingale
factors. Different positive deterministic reward coefficients cancel. -/
theorem joint_reward_anchor_limits
    {Component Space : Type*} [Fintype Component] [MeasurableSpace Component]
    [MeasurableSingletonClass Component] [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (edgeCount vertexCount : ℕ → Component → ℝ) (totalEdges totalVertices : ℕ → ℝ)
    (growth edgeCoefficient vertexCoefficient rootMass : ℝ)
    (componentMass : Component → ℝ) (growthNonzero : growth ≠ 0)
    (edgePositive : 0 < edgeCoefficient) (vertexPositive : 0 < vertexCoefficient)
    (rootPositive : 0 < rootMass)
    (edgeNonnegative : ∀ depth component, 0 ≤ edgeCount depth component / totalEdges depth)
    (vertexNonnegative : ∀ depth component, 0 ≤ vertexCount depth component / totalVertices depth)
    (edgePartition : ∀ depth, ∑ component, edgeCount depth component / totalEdges depth = 1)
    (vertexPartition : ∀ depth, ∑ component, vertexCount depth component / totalVertices depth = 1)
    (massNonnegative : ∀ component, 0 ≤ componentMass component / rootMass)
    (massPartition : ∑ component, componentMass component / rootMass = 1)
    (edgeLimits : ∀ component, Tendsto (fun depth => edgeCount depth component / growth ^ depth)
      atTop (𝓝 (edgeCoefficient * componentMass component)))
    (vertexLimits : ∀ component, Tendsto (fun depth => vertexCount depth component / growth ^ depth)
      atTop (𝓝 (vertexCoefficient * componentMass component)))
    (totalEdgeLimit : Tendsto (fun depth => totalEdges depth / growth ^ depth)
      atTop (𝓝 (edgeCoefficient * rootMass)))
    (totalVertexLimit : Tendsto (fun depth => totalVertices depth / growth ^ depth)
      atTop (𝓝 (vertexCoefficient * rootMass)))
    (anchor : Component → Space) :
    Tendsto (fun depth => levyProkhorovEDist
      ((finiteWeightPMF (fun component => edgeCount depth component / totalEdges depth)
        (edgeNonnegative depth) (edgePartition depth)).toMeasure.map anchor)
      ((finiteWeightPMF (fun component => componentMass component / rootMass)
        massNonnegative massPartition).toMeasure.map anchor)) atTop (𝓝 0) ∧
    Tendsto (fun depth => levyProkhorovEDist
      ((finiteWeightPMF (fun component => vertexCount depth component / totalVertices depth)
        (vertexNonnegative depth) (vertexPartition depth)).toMeasure.map anchor)
      ((finiteWeightPMF (fun component => componentMass component / rootMass)
        massNonnegative massPartition).toMeasure.map anchor)) atTop (𝓝 0) := by
  constructor
  · exact IGSIII.Geometry.levyProkhorovEDist_finiteWeightPMF_map_tendsto_zero _ _
      edgeNonnegative massNonnegative edgePartition massPartition
      (fun component => reward_constant_cancels _ _ _ _ _ _ growthNonzero edgePositive rootPositive
        (edgeLimits component) totalEdgeLimit) anchor (measurable_of_finite _)
  · exact IGSIII.Geometry.levyProkhorovEDist_finiteWeightPMF_map_tendsto_zero _ _
      vertexNonnegative massNonnegative vertexPartition massPartition
      (fun component => reward_constant_cancels _ _ _ _ _ _ growthNonzero vertexPositive rootPositive
        (vertexLimits component) totalVertexLimit) anchor (measurable_of_finite _)

end
end IGSIII34.Diffusion

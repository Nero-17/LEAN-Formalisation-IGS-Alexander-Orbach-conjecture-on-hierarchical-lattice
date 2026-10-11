import IGSIII34.Spectral.BoundaryLocalEvaluationCompletion20261011
import IGSIII34.Spectral.NaturalPhysicalCylinderMeshCompletion20261011
import IGSIII34.Spectral.ActualBoundaryTypicalMassCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem inverse_clock_mass_bound_completion20261011
    (radius resistance slack mass : ℝ) (radiusPositive : 0 < radius)
    (resistancePositive : 0 < resistance) (slackPositive : 0 < slack)
    (massPositive : 0 < mass) (depth : ℕ)
    (massLower : (slack^depth)⁻¹ ≤ mass * radius^depth) :
    1 / ((radius * resistance)^depth * mass) ≤ (slack / resistance)^depth := by
  apply (div_le_iff₀ (mul_pos (pow_pos (mul_pos radiusPositive resistancePositive) depth) massPositive)).mpr
  have product := mul_le_mul_of_nonneg_right massLower (pow_pos slackPositive depth).le
  have normalization : (slack^depth)⁻¹ * slack^depth = 1 := inv_mul_cancel₀ (pow_pos slackPositive depth).ne'
  rw [normalization] at product
  calc
    _ ≤ mass * radius^depth * slack^depth := product
    _ = _ := by rw [div_pow, mul_pow]; field_simp [(pow_pos resistancePositive depth).ne']

theorem clock_upper_constant_absorption_completion20261011
    (resistance slack tolerance coefficient : ℝ) (resistancePositive : 0 < resistance)
    (slackPositive : 0 < slack) (slackBelow : slack < tolerance) :
    ∀ᶠ depth in atTop, coefficient * (slack / resistance)^depth ≤ tolerance^depth / resistance^depth := by
  have ratioGreater : 1 < tolerance / slack := (one_lt_div slackPositive).mpr slackBelow
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt ratioGreater).eventually (eventually_ge_atTop coefficient)]
    with depth large
  have multiplied := mul_le_mul_of_nonneg_right large (pow_pos (div_pos slackPositive resistancePositive) depth).le
  have normalized : (tolerance / slack)^depth * (slack / resistance)^depth = tolerance^depth / resistance^depth := by
    rw [← mul_pow, ← div_pow]
    congr 1
    field_simp [slackPositive.ne', resistancePositive.ne']
  simpa only [normalized] using multiplied

theorem boundary_same_prefix_distance_completion20261011
    {Choice Space : Type*} [MeasurableSpace Choice] [MeasurableSingletonClass Choice] [Countable Choice] [PseudoMetricSpace Space]
    (boundary : Measure (Π depth, Fin depth → Choice))
    (anchors : ∀ depth, (Fin (depth + 1) → Choice) → Space)
    (realization : (Π depth, Fin depth → Choice) → Space)
    (threshold : ℕ) (coefficient eta : ℝ)
    (mesh : ∀ᵐ path ∂boundary, ∀ depth, threshold ≤ depth →
      dist (anchors depth (path (depth + 1))) (realization path) ≤ coefficient * eta^(depth + 1)) :
    ∀ᵐ path ∂boundary, ∀ depth, threshold ≤ depth →
      ∀ᵐ other ∂boundary.restrict {other | other (depth + 1) = path (depth + 1)},
        dist (realization path) (realization other) ≤ 2 * coefficient * eta^(depth + 1) := by
  filter_upwards [mesh] with path estimates
  intro depth beyond
  have cylinderMeasurable : MeasurableSet {other : Π depth, Fin depth → Choice | other (depth + 1) = path (depth + 1)} :=
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  filter_upwards [ae_restrict_of_ae mesh, ae_restrict_mem cylinderMeasurable] with other bounds same
  have first := estimates depth beyond
  have second := bounds depth beyond
  rw [same] at second
  have triangle := dist_triangle (realization path) (anchors depth (path (depth + 1))) (realization other)
  rw [dist_comm (realization path) (anchors depth (path (depth + 1)))] at triangle
  linarith

end
end IGSIII34.Spectral

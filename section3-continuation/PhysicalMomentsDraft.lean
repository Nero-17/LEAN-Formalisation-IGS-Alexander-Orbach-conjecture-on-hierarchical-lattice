import IGSIII34.Percolation.PhysicalOrbit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped NNReal ENNReal

theorem electricalIteration_eq_scale_mul_normalized (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    electricalIterationNNReal rule marks depth [] =
      electricalOrbitScale rule parameter positive belowOne fixedPoint depth *
        normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks := by
  unfold normalizedPhysicalResistance
  rw [← mul_assoc, mul_inv_cancel₀
    (electricalOrbitScale_positive rule classical parameter positive belowOne fixedPoint depth).ne', one_mul]

theorem normalizedPhysicalResistance_mean_one (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    (∫ marks, (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) = 1 := by
  have mapped := integral_map
    (μ := independentInnovationLaw rule parameter positive belowOne fixedPoint)
    (φ := normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth)
    (f := fun value : ℝ≥0 => (value : ℝ))
    (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth).aemeasurable
    NNReal.continuous_coe.measurable.aestronglyMeasurable
  rw [normalizedPhysicalResistance_law rule parameter positive belowOne fixedPoint depth] at mapped
  exact mapped.symm.trans (normalizedElectricalOrbit_mean_one rule classical parameter positive belowOne fixedPoint depth)

theorem electricalOrbitScale_eq_actual_mean (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) =
      ∫ marks, electricalIteration rule marks depth []
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
  symm
  calc
    _ = ∫ marks, (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) *
        (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ)
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
      apply integral_congr_ae
      filter_upwards with marks
      exact congrArg (fun value : ℝ≥0 => (value : ℝ))
        (electricalIteration_eq_scale_mul_normalized rule classical parameter positive belowOne fixedPoint depth marks)
    _ = _ := by rw [integral_const_mul, normalizedPhysicalResistance_mean_one rule classical parameter positive belowOne fixedPoint depth, mul_one]

theorem normalizedPhysicalResistance_uniform_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (power : ℕ) :
    ∃ bound : ℝ≥0, ∀ depth,
      (∫⁻ marks, (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks : ℝ≥0∞)^power
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) ≤ bound := by
  obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_moment rule classical parameter positive belowOne fixedPoint power
  refine ⟨bound, fun depth => ?_⟩
  have mapped := lintegral_map (μ := independentInnovationLaw rule parameter positive belowOne fixedPoint)
    (f := fun value : ℝ≥0 => (value : ℝ≥0∞)^power)
    (g := normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth)
    (measurable_id.coe_nnreal_ennreal.pow_const power)
    (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth)
  rw [normalizedPhysicalResistance_law rule parameter positive belowOne fixedPoint depth] at mapped
  exact mapped.symm.trans_le (momentBound depth)

theorem normalizedPhysicalResistance_positive_ae (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      0 < normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth marks := by
  filter_upwards [electricalIteration_positive_ae rule parameter positive belowOne fixedPoint depth []] with marks resistancePositive
  apply mul_pos
  · exact inv_pos.mpr (electricalOrbitScale_positive rule classical parameter positive belowOne fixedPoint depth)
  · exact_mod_cast resistancePositive

theorem normalizedElectricalOrbit_positive_ae (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    ∀ᵐ value ∂(normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0), 0 < value := by
  rw [← normalizedPhysicalResistance_law rule parameter positive belowOne fixedPoint depth]
  exact (ae_map_iff (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth).aemeasurable
    (measurableSet_lt measurable_const measurable_id)).mpr
    (normalizedPhysicalResistance_positive_ae rule classical parameter positive belowOne fixedPoint depth)

end
end IGSIII34.Percolation

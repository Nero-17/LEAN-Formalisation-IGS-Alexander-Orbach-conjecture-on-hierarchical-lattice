import IGSIII34.Probability.MomentConstraints
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory BoundedContinuousFunction Filter Set _root_.Topology
open scoped NNReal ENNReal

theorem integrable_coe_of_secondMoment_bound (law : ProbabilityMeasure ℝ≥0)
    (bound : ℝ≥0)
    (momentBound : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound) :
    Integrable (fun value : ℝ≥0 => (value : ℝ)) (law : Measure ℝ≥0) := by
  have squareIntegrable : Integrable (fun value : ℝ≥0 => (value : ℝ) ^ 2)
      (law : Measure ℝ≥0) := by
    have finite : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top momentBound
    have result := integrable_toReal_of_lintegral_ne_top
      (measurable_id.coe_nnreal_ennreal.pow_const 2).aemeasurable finite
    simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, id_eq] using result
  apply (integrable_const (1 : ℝ)).add squareIntegrable |>.mono'
    NNReal.continuous_coe.measurable.aestronglyMeasurable
  filter_upwards [] with value
  change |(value : ℝ)| ≤ 1 + (value : ℝ) ^ 2
  calc
    _ = (value : ℝ) := NNReal.abs_eq value
    _ ≤ _ := by nlinarith [sq_nonneg ((value : ℝ) - 1)]

theorem firstMoment_truncation_error (law : ProbabilityMeasure ℝ≥0)
    (bound : ℝ≥0)
    (momentBound : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound)
    {truncation : ℕ} (truncationPositive : 0 < truncation) :
    |(∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) -
      ∫ value : ℝ≥0, (min value (truncation : ℝ≥0) : ℝ) ∂(law : Measure ℝ≥0)| ≤
        (bound : ℝ) / truncation := by
  have firstIntegrable := integrable_coe_of_secondMoment_bound law bound momentBound
  have squareIntegrable : Integrable (fun value : ℝ≥0 => (value : ℝ) ^ 2)
      (law : Measure ℝ≥0) := by
    have finite : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top momentBound
    have result := integrable_toReal_of_lintegral_ne_top
      (measurable_id.coe_nnreal_ennreal.pow_const 2).aemeasurable finite
    simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, id_eq] using result
  have truncatedIntegrable' : Integrable
      (fun value : ℝ≥0 => (min value (truncation : ℝ≥0) : ℝ)) (law : Measure ℝ≥0) := by
    apply firstIntegrable.mono' (NNReal.continuous_coe.comp (continuous_id.min continuous_const)).measurable.aestronglyMeasurable
    filter_upwards [] with value
    change |((min value (truncation : ℝ≥0) : ℝ≥0) : ℝ)| ≤ (value : ℝ)
    calc
      _ = ((min value (truncation : ℝ≥0) : ℝ≥0) : ℝ) := NNReal.abs_eq _
      _ ≤ (value : ℝ) := by exact_mod_cast min_le_left value (truncation : ℝ≥0)
  have truncatedBelow : (∫ value : ℝ≥0, (min value (truncation : ℝ≥0) : ℝ) ∂(law : Measure ℝ≥0)) ≤
      ∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0) := by
    exact integral_mono truncatedIntegrable' firstIntegrable (fun value => by exact_mod_cast min_le_left value _)
  rw [abs_of_nonneg (sub_nonneg.mpr truncatedBelow), ← integral_sub firstIntegrable truncatedIntegrable']
  have boundIntegral : (∫ value : ℝ≥0, (value : ℝ) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound := by
    have result := integral_coe_le_of_lintegral_coe_le
      (f := fun value : ℝ≥0 => value ^ 2) (b := bound) (by simpa only [ENNReal.coe_pow] using momentBound)
    convert result using 1
    congr 1
  calc
    _ ≤ ∫ value : ℝ≥0, (value : ℝ) ^ 2 / truncation ∂(law : Measure ℝ≥0) := by
      apply integral_mono (firstIntegrable.sub truncatedIntegrable') (squareIntegrable.div_const _)
      intro value
      have truncationPositive' : (0 : ℝ) < truncation := by exact_mod_cast truncationPositive
      change (value : ℝ) - min (value : ℝ) (truncation : ℝ) ≤ (value : ℝ) ^ 2 / truncation
      by_cases below : (value : ℝ) ≤ truncation
      · rw [min_eq_left below, sub_self]
        positivity
      · rw [min_eq_right (le_of_not_ge below)]
        apply (le_div_iff₀ truncationPositive').mpr
        nlinarith [sq_nonneg ((value : ℝ) - truncation)]
    _ = (∫ value : ℝ≥0, (value : ℝ) ^ 2 ∂(law : Measure ℝ≥0)) / truncation := integral_div _ _
    _ ≤ (bound : ℝ) / truncation := div_le_div_of_nonneg_right boundIntegral (Nat.cast_nonneg _)

def truncatedFirstMomentTest (truncation : ℕ) : ℝ≥0 →ᵇ ℝ :=
  BoundedContinuousFunction.comp (fun value : ℝ≥0 => (value : ℝ)) NNReal.isometry_coe.lipschitz
    (boundedTruncation (fun value : ℝ≥0 => value) continuous_id truncation)

theorem continuous_firstMoment_on_secondMoment_sublevel (bound : ℝ≥0) :
    Continuous (fun law : {law : ProbabilityMeasure ℝ≥0 |
        (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound} =>
      ∫ value : ℝ≥0, (value : ℝ) ∂(law.val : Measure ℝ≥0)) := by
  apply continuous_of_uniform_approx_of_continuous
  intro entourage entourageMember
  obtain ⟨epsilon, epsilonPositive, ballSubset⟩ := Metric.mem_uniformity_dist.mp entourageMember
  obtain ⟨truncation, truncationLarge⟩ := exists_nat_gt (max 1 ((bound : ℝ) / epsilon))
  have truncationPositive : 0 < truncation := by
    have : (1 : ℝ) < truncation := (le_max_left _ _).trans_lt truncationLarge
    exact_mod_cast (lt_trans zero_lt_one this)
  have truncationPositive' : (0 : ℝ) < truncation := by exact_mod_cast truncationPositive
  have errorSmall : (bound : ℝ) / truncation < epsilon := by
    apply (div_lt_iff₀ truncationPositive').mpr
    have large := (div_lt_iff₀ epsilonPositive).mp ((le_max_right _ _).trans_lt truncationLarge)
    simpa only [mul_comm] using large
  refine ⟨fun law => ∫ value, truncatedFirstMomentTest truncation value ∂(law.val : Measure ℝ≥0),
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (truncatedFirstMomentTest truncation)).comp continuous_subtype_val, ?_⟩
  intro law
  apply ballSubset
  change dist (∫ value : ℝ≥0, (value : ℝ) ∂(law.val : Measure ℝ≥0))
    (∫ value : ℝ≥0, truncatedFirstMomentTest truncation value ∂(law.val : Measure ℝ≥0)) < epsilon
  rw [Real.dist_eq]
  exact (firstMoment_truncation_error law.val bound law.property truncationPositive).trans_lt errorSmall

theorem isCompact_secondMoment_sublevel (bound : ℝ≥0) :
    IsCompact {law : ProbabilityMeasure ℝ≥0 |
      (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound} := by
  have closed : IsClosed {law : ProbabilityMeasure ℝ≥0 |
      (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound} := by
    convert isClosed_lintegral_sublevel (fun value : ℝ≥0 => value ^ 2) (continuous_id.pow 2) bound using 1
    ext law
    simp only [Set.mem_setOf_eq]
    have equality : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) =
        ∫⁻ value : ℝ≥0, ((value ^ 2 : ℝ≥0) : ℝ≥0∞) ∂(law : Measure ℝ≥0) :=
      lintegral_congr (fun value => (ENNReal.coe_pow value 2).symm)
    rw [equality]
  apply (isCompact_firstMoment_sublevel (1 + bound)).of_isClosed_subset closed
  intro law momentBound
  change (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound at momentBound
  calc
    (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) ≤
        ∫⁻ value, 1 + (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0) := by
      apply lintegral_mono
      intro value
      have realBound : (value : ℝ) ≤ 1 + (value : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((value : ℝ) - 1)]
      have nnrealBound : value ≤ 1 + value ^ 2 := by exact_mod_cast realBound
      simpa only [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_pow] using ENNReal.coe_le_coe.mpr nnrealBound
    _ = 1 + ∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0) := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ (1 + bound : ℝ≥0) := by
      simpa only [ENNReal.coe_add, ENNReal.coe_one] using add_le_add le_rfl momentBound

theorem isCompact_meanOne_secondMoment_sublevel (bound : ℝ≥0) :
    IsCompact {law : ProbabilityMeasure ℝ≥0 |
      (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound ∧
      (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1} := by
  let domain := {law : ProbabilityMeasure ℝ≥0 |
      (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound}
  letI : CompactSpace domain := isCompact_iff_compactSpace.mp (isCompact_secondMoment_sublevel bound)
  have closed : IsClosed {law : domain |
      (∫ value : ℝ≥0, (value : ℝ) ∂(law.val : Measure ℝ≥0)) = 1} :=
    isClosed_eq (continuous_firstMoment_on_secondMoment_sublevel bound) continuous_const
  have compactImage := closed.isCompact.image (continuous_subtype_val : Continuous (Subtype.val : domain → ProbabilityMeasure ℝ≥0))
  convert compactImage using 1
  ext law
  simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, domain,
    exists_prop]

end
end IGSIII34.Probability

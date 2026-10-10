import IGSIII.Chemical.EndogenousEnvelopeBarrier
import IGSIII.Chemical.OrbitDeterministicBounds
import IGSIII.Probability.DoubleExponentialEnvelope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality MeasureTheory Set IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal

theorem chemicalOrbit_supremum_memLp_of_endogenous_field
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueFixed : normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (comparison : ∀ member ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
      lower • value ≤ member ∧ member ≤ upper • value)
    (order : ℝ≥0∞) [Fact (1 ≤ order)] (orderFinite : order ≠ ∞) :
    MemLp (fun marks => ⨆ depth, chemicalOrbit rule p positive belowOne fixedPoint growth depth marks)
      order (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ depth,
      chemicalOrbit rule p positive belowOne fixedPoint growth depth marks ≤
        ⨆ index, chemicalOrbit rule p positive belowOne fixedPoint growth index marks := by
  have orderPositive : order ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have valueMemLp := (chemical_value_all_finite_lp_of_omega_comparison_bounds rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive meanBounds value valuePositive lower upper lowerPositive upperPositive
    comparison).1 order orderPositive orderFinite |>.1
  obtain ⟨nonempty, _⟩ := chemicalOmegaSet_properties rule classical p positive belowOne fixedPoint
    constant growth growthPositive meanBounds
  obtain ⟨base, baseMember⟩ := nonempty
  have countPositive : (0 : ℝ) < (((rule.edges + 3) ^ 4 : ℕ) : ℝ) := by positivity
  have ratioPositive : 0 < (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨scale, scalePositive, pairedIntegrable, pairedBound⟩ :=
    exists_unit_value_paired_barrier_of_omega_lower_bound rule classical p positive belowOne fixedPoint
      constant growth growthPositive meanBounds value base baseMember valuePositive upper⁻¹
      (inv_pos.mpr upperPositive) (lp_inv_smul_le_of_le_smul upper upperPositive (comparison base baseMember).2)
      ratioPositive
  have ratioIdentity : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) *
      (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ = 1 / 2 := by field_simp
  let exceptions : ℕ → Set ((List (Fin rule.edges) × Bool) → FiniteNetwork.Configuration rule.edges) :=
    fun depth => {marks | scale * value marks < chemicalOrbit rule p positive belowOne fixedPoint growth depth marks}
  have eventsMeasurable : ∀ depth, MeasurableSet (exceptions depth) := fun depth =>
    measurableSet_lt ((Lp.stronglyMeasurable value).measurable.const_mul scale)
      (Lp.stronglyMeasurable (chemicalOrbit rule p positive belowOne fixedPoint growth depth)).measurable
  have probabilities : ∀ depth, (independentInnovationLaw rule p positive belowOne fixedPoint) (exceptions depth) ≤
      ENNReal.ofReal ((2 : ℝ) * (1 / 2 : ℝ) ^
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ depth)) := by
    intro depth
    cases depth with
    | zero => simpa only [pow_zero, pow_one, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),
        ENNReal.ofReal_one] using
        (show (independentInnovationLaw rule p positive belowOne fixedPoint) (exceptions 0) ≤ 1 from prob_le_one)
    | succ depth =>
      have bound := chemicalOrbit_fixed_comparison_probability_bound rule classical p positive belowOne fixedPoint
        growth growthPositive value valueFixed ratioPositive.le pairedIntegrable pairedBound
        (by rw [ratioIdentity]; norm_num) depth
      rw [ratioIdentity] at bound
      have realBound : (independentInnovationLaw rule p positive belowOne fixedPoint).real (exceptions (depth + 1)) ≤
          2 * (1 / 2 : ℝ) ^ (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) := by
        convert bound using 1 <;> ring
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans_le (ENNReal.ofReal_le_ofReal realBound)
  let bound : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    (valueMemLp.const_mul scale).toLp (fun marks => scale * value marks)
  have boundEquality := MemLp.coeFn_toLp (valueMemLp.const_mul scale)
  have boundNonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 ≤ bound marks := by
    filter_upwards [boundEquality, valuePositive] with marks equality positivity
    rw [equality]
    exact mul_nonneg scalePositive.le positivity.le
  have deterministic := chemicalOrbit_ae_deterministic_bounds rule p positive belowOne fixedPoint growth growthPositive
  have sequenceBound : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ depth,
      chemicalOrbit rule p positive belowOne fixedPoint growth depth marks ≤ bound marks +
        (exceptions depth).indicator (fun _ => ((rule.edges : ℝ) / growth) ^ depth) marks := by
    filter_upwards [boundEquality, valuePositive, deterministic] with marks equality positivity bounds
    intro depth
    by_cases bad : marks ∈ exceptions depth
    · rw [Set.indicator_of_mem bad]
      exact (bounds depth).2.trans (le_add_of_nonneg_left (by rw [equality]; exact mul_nonneg scalePositive.le positivity.le))
    · rw [Set.indicator_of_notMem bad, add_zero, equality]
      exact le_of_not_gt bad
  have summableNorms := indicator_norms_summable_of_double_exponential
    (independentInnovationLaw rule p positive belowOne fixedPoint) order orderPositive orderFinite exceptions eventsMeasurable
    1 ((rule.edges : ℝ) / growth) 2 (1 / 2) zero_le_one
    (div_nonneg (Nat.cast_nonneg _) growthPositive.le) (by norm_num) (by norm_num) (by norm_num)
    _ classical.scale probabilities
  simp only [one_mul] at summableNorms
  obtain ⟨dominator, _, dominates⟩ := exists_lp_dominator_of_summable_exceptions
    (independentInnovationLaw rule p positive belowOne fixedPoint) order
    (fun depth marks => chemicalOrbit rule p positive belowOne fixedPoint growth depth marks) bound boundNonnegative
    exceptions eventsMeasurable (fun depth => ((rule.edges : ℝ) / growth) ^ depth)
    (fun depth => pow_nonneg (div_nonneg (Nat.cast_nonneg _) growthPositive.le) depth) sequenceBound summableNorms
  exact supremum_memLp_of_lp_dominator _ order _
    (fun depth => (Lp.stronglyMeasurable (chemicalOrbit rule p positive belowOne fixedPoint growth depth)).measurable)
    (deterministic.mono (fun _ bounds depth => (bounds depth).1)) dominator dominates

end IGSIII.Chemical.Substitution

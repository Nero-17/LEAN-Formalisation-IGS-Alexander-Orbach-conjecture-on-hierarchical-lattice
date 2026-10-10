import IGSIII.Chemical.SmallBall.ChemicalOmegaPairedMarginals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution
open scoped BigOperators ENNReal

noncomputable section

theorem chemicalOrbit_lintegral_response_le (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth) (response : ℝ → ℝ≥0∞) (bound : ℝ≥0∞)
    (seedBound : response 1 ≤ bound)
    (finiteBounds : ∀ depth, (∑ configuration,
      ENNReal.ofReal ((rule.generation depth).network.conditionalCellWeight p true configuration) *
        response (growthScaledDistance rule growth depth configuration)) ≤ bound) (depth : ℕ) :
    (∫⁻ marks, response (chemicalOrbit rule p positive lessOne fixedPoint growth depth marks)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ bound := by
  cases depth with
  | zero =>
      have equality : chemicalOrbit rule p positive lessOne fixedPoint growth 0 = chemicalUnitLp rule p positive lessOne fixedPoint 2 := rfl
      rw [equality]
      calc
        _ = ∫⁻ _marks, response 1 ∂independentInnovationLaw rule p positive lessOne fixedPoint :=
          lintegral_congr_ae ((chemicalUnitLp_ae rule p positive lessOne fixedPoint 2).mono
            (fun _ equality => congrArg response equality))
        _ = response 1 := by simp
        _ ≤ bound := seedBound
  | succ depth =>
      rw [chemicalOrbit_tail_eq_actual rule classical p positive lessOne fixedPoint growth growthNonnegative depth]
      calc
        _ = ∫⁻ marks, response (growthScaledDistance rule growth depth
            (markedGenerationConfiguration rule marks depth [] true))
              ∂independentInnovationLaw rule p positive lessOne fixedPoint :=
          lintegral_congr_ae ((markedObservableLp_ae rule p positive lessOne fixedPoint depth [] true
            (growthScaledDistance rule growth depth)).mono (fun _ equality => congrArg response equality))
        _ = ∑ configuration, ENNReal.ofReal ((rule.generation depth).network.conditionalCellWeight p true configuration) *
            response (growthScaledDistance rule growth depth configuration) :=
          independentInnovationLaw_marked_lintegral rule p positive lessOne fixedPoint depth [] true
            (fun configuration => response (growthScaledDistance rule growth depth configuration))
        _ ≤ bound := finiteBounds depth

theorem exists_uniform_chemicalOrbit_exponential_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (parameter : ℝ) (parameterNonnegative : 0 ≤ parameter) :
    ∃ bound : ℝ, ∀ depth : ℕ,
      (∫⁻ marks, ENNReal.ofReal (Real.exp (parameter * chemicalOrbit rule p positive lessOne fixedPoint growth depth marks))
        ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal bound := by
  obtain ⟨bound, finiteValid⟩ := exists_uniform_growth_scaled_exponential_moment rule classical p positive lessOne fixedPoint
    constant growth constantPositive growthPositive meanBounds parameter parameterNonnegative
  refine ⟨max (Real.exp parameter) bound, fun depth => ?_⟩
  apply chemicalOrbit_lintegral_response_le rule classical p positive lessOne fixedPoint growth growthPositive.le
    (fun value => ENNReal.ofReal (Real.exp (parameter * value))) (ENNReal.ofReal (max (Real.exp parameter) bound)) _ _ depth
  · simpa only [mul_one] using ENNReal.ofReal_le_ofReal (le_max_left (Real.exp parameter) bound)
  · intro depth
    rw [finite_ofReal_weighted_sum _ _
      ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true)
      (fun _ => Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((finiteValid depth).trans (le_max_right _ _))

theorem exponential_memLp_two_of_lintegral_bound
    {Sample : Type*} [MeasurableSpace Sample] (μ : Measure Sample) (value : Lp ℝ 2 μ)
    {bound : ℝ≥0∞} (boundFinite : bound ≠ ∞)
    (momentBound : (∫⁻ sample, ENNReal.ofReal (Real.exp (2 * value sample)) ∂μ) ≤ bound) :
    MemLp (fun sample => Real.exp (value sample)) 2 μ := by
  apply (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable value).measurable.exp.aestronglyMeasurable).mpr
  have integrable : Integrable (fun sample => Real.exp (2 * value sample)) μ := by
    refine ⟨((Lp.stronglyMeasurable value).measurable.const_mul 2).exp.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun sample => Real.exp_nonneg (2 * value sample)))).mpr
      (lt_of_le_of_lt momentBound (lt_top_iff_ne_top.mpr boundFinite))
  convert integrable using 1
  funext sample
  rw [← Real.exp_nat_mul]
  norm_num

end
end IGSIII.Chemical.SmallBall
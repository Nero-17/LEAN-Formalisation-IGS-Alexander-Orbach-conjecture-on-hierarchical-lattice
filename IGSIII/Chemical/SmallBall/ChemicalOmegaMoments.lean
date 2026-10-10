import IGSIII.Chemical.ChemicalOmega
import IGSIII.Chemical.SmallBall.MomentLimits
import IGSIII.Chemical.SubstitutionPaths.MarkedConfigurationLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution
open scoped BigOperators ENNReal Topology

noncomputable section

theorem finite_ofReal_weighted_sum {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (responseNonnegative : ∀ outcome, 0 ≤ response outcome) :
    (∑ outcome, ENNReal.ofReal (weight outcome) * ENNReal.ofReal (response outcome)) =
      ENNReal.ofReal (∑ outcome, weight outcome * response outcome) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun outcome _ => mul_nonneg (weightNonnegative outcome) (responseNonnegative outcome))]
  exact Finset.sum_congr rfl (fun outcome _ => (ENNReal.ofReal_mul (weightNonnegative outcome)).symm)

theorem chemicalOmega_lintegral_continuous_response_le (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (response : ℝ → ℝ≥0∞) (continuous : Continuous response) (bound : ℝ≥0∞)
    (seedBound : response 1 ≤ bound)
    (finiteBounds : ∀ depth, (∑ configuration,
      ENNReal.ofReal ((rule.generation depth).network.conditionalCellWeight p true configuration) *
        response (growthScaledDistance rule growth depth configuration)) ≤ bound)
    (point : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (membership : point ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
    (∫⁻ marks, response (point marks) ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ bound := by
  apply orbitClusterSet_lintegral_continuous_response_le _ _ point membership response continuous bound
  intro depth
  cases depth with
  | zero =>
      have equality : chemicalOrbit rule p positive lessOne fixedPoint growth 0 = chemicalUnitLp rule p positive lessOne fixedPoint 2 := rfl
      rw [equality]
      have integralEquality : (∫⁻ marks, response (chemicalUnitLp rule p positive lessOne fixedPoint 2 marks)
          ∂independentInnovationLaw rule p positive lessOne fixedPoint) = response 1 := by
        calc
          _ = ∫⁻ _marks, response 1 ∂independentInnovationLaw rule p positive lessOne fixedPoint :=
            lintegral_congr_ae ((chemicalUnitLp_ae rule p positive lessOne fixedPoint 2).mono
              (fun _ equality => congrArg response equality))
          _ = _ := by simp
      exact integralEquality.trans_le seedBound
  | succ depth =>
      rw [chemicalOrbit_tail_eq_actual rule classical p positive lessOne fixedPoint growth growthNonnegative depth]
      have integralEquality : (∫⁻ marks,
          response (markedObservableLp rule p positive lessOne fixedPoint depth [] true (growthScaledDistance rule growth depth) marks)
            ∂independentInnovationLaw rule p positive lessOne fixedPoint) =
          ∑ configuration, ENNReal.ofReal ((rule.generation depth).network.conditionalCellWeight p true configuration) *
            response (growthScaledDistance rule growth depth configuration) := by
        calc
          _ = ∫⁻ marks, response (growthScaledDistance rule growth depth
              (markedGenerationConfiguration rule marks depth [] true))
                ∂independentInnovationLaw rule p positive lessOne fixedPoint :=
            lintegral_congr_ae ((markedObservableLp_ae rule p positive lessOne fixedPoint depth [] true
              (growthScaledDistance rule growth depth)).mono (fun _ equality => congrArg response equality))
          _ = _ := independentInnovationLaw_marked_lintegral rule p positive lessOne fixedPoint depth [] true
            (fun configuration => response (growthScaledDistance rule growth depth configuration))
      exact integralEquality.trans_le (finiteBounds depth)

theorem exists_uniform_chemicalOmega_exponential_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (parameter : ℝ) (parameterNonnegative : 0 ≤ parameter) :
    ∃ bound : ℝ, ∀ point ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
      (∫⁻ marks, ENNReal.ofReal (Real.exp (parameter * point marks))
        ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal bound := by
  obtain ⟨bound, finiteValid⟩ := exists_uniform_growth_scaled_exponential_moment rule classical p positive lessOne fixedPoint
    constant growth constantPositive growthPositive meanBounds parameter parameterNonnegative
  refine ⟨max (Real.exp parameter) bound, fun point membership => ?_⟩
  apply chemicalOmega_lintegral_continuous_response_le rule classical p positive lessOne fixedPoint growth growthPositive.le
    (fun value => ENNReal.ofReal (Real.exp (parameter * value)))
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    (ENNReal.ofReal (max (Real.exp parameter) bound)) _ _ point membership
  · simpa only [mul_one] using ENNReal.ofReal_le_ofReal (le_max_left (Real.exp parameter) bound)
  · intro depth
    rw [finite_ofReal_weighted_sum _ _
      ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true)
      (fun _ => Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((finiteValid depth).trans (le_max_right _ _))

theorem exists_uniform_chemicalOmega_inverse_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) (power : ℕ) :
    ∃ bound : ℝ, ∀ point ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
      (∫⁻ marks, (ENNReal.ofReal (point marks))⁻¹ ^ power
        ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal bound := by
  obtain ⟨bound, finiteValid⟩ := exists_uniform_growth_scaled_inverse_moment rule classical p positive lessOne fixedPoint
    constant growth growthPositive meanBounds power
  refine ⟨max 1 bound, fun point membership => ?_⟩
  apply chemicalOmega_lintegral_continuous_response_le rule classical p positive lessOne fixedPoint growth growthPositive.le
    (fun value => (ENNReal.ofReal value)⁻¹ ^ power)
    ((ENNReal.continuous_pow power).comp ENNReal.continuous_ofReal.fun_inv)
    (ENNReal.ofReal (max 1 bound)) _ _ point membership
  · simpa only [ENNReal.ofReal_one, inv_one, one_pow] using ENNReal.ofReal_le_ofReal (le_max_left (1 : ℝ) bound)
  · intro depth
    have identity : (∑ configuration,
        ENNReal.ofReal ((rule.generation depth).network.conditionalCellWeight p true configuration) *
          (ENNReal.ofReal (growthScaledDistance rule growth depth configuration))⁻¹ ^ power) =
        ENNReal.ofReal (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
          (growthScaledDistance rule growth depth configuration)⁻¹ ^ power) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun configuration _ => mul_nonneg
        ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
        (pow_nonneg (inv_nonneg.mpr (growthScaledDistance_nonnegative rule growth growthPositive.le depth configuration)) power))]
      apply Finset.sum_congr rfl
      intro configuration _
      by_cases crossing : (rule.generation depth).network.crosses configuration = true
      · have distancePositive : 0 < growthScaledDistance rule growth depth configuration := by
          apply div_pos _ (pow_pos growthPositive _)
          exact_mod_cast (((rule.generation depth).network.crosses_eq_true configuration).mp crossing).pos_dist_of_ne
            (rule.generation depth).network.terminals_distinct
        rw [ENNReal.ofReal_mul ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration),
          ENNReal.ofReal_pow (inv_nonneg.mpr distancePositive.le), ENNReal.ofReal_inv_of_pos distancePositive]
      · simp [conditionalCellWeight, crossing]
    rw [identity]
    exact ENNReal.ofReal_le_ofReal ((finiteValid depth).trans (le_max_right _ _))

theorem chemicalOmega_ae_positive (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (point : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (membership : point ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < point marks := by
  obtain ⟨bound, valid⟩ := exists_uniform_chemicalOmega_inverse_moment rule classical p positive lessOne fixedPoint
    constant growth growthPositive meanBounds 1
  apply ae_positive_of_lintegral_inverse_ofReal_lt_top _ point (Lp.aestronglyMeasurable _).aemeasurable
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by simpa only [pow_one] using valid point membership)

theorem exists_uniform_chemicalOmega_laplace_decay (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    {target : ℝ} (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ point ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
      (∫⁻ marks, ENNReal.ofReal (Real.exp (-parameter * point marks))
        ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal target := by
  obtain ⟨parameter, parameterPositive, finiteValid⟩ := exists_uniform_growth_scaled_laplace_decay
    rule classical p positive lessOne fixedPoint constant growth growthPositive meanBounds targetPositive
  refine ⟨max parameter (-Real.log target), parameterPositive.trans_le (le_max_left _ _), fun point membership => ?_⟩
  apply chemicalOmega_lintegral_continuous_response_le rule classical p positive lessOne fixedPoint growth growthPositive.le
    (fun value => ENNReal.ofReal (Real.exp (-max parameter (-Real.log target) * value)))
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    (ENNReal.ofReal target) _ _ point membership
  · simp only [mul_one]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Real.exp (Real.log target) := Real.exp_le_exp.mpr (by linarith [le_max_right parameter (-Real.log target)])
      _ = target := Real.exp_log targetPositive
  · intro depth
    rw [finite_ofReal_weighted_sum _ _
      ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true)
      (fun _ => Real.exp_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    refine (Finset.sum_le_sum (fun configuration _ => ?_)).trans (finiteValid depth)
    apply mul_le_mul_of_nonneg_left _
      ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left parameter (-Real.log target)))
      (growthScaledDistance_nonnegative rule growth growthPositive.le depth configuration)

end
end IGSIII.Chemical.SmallBall

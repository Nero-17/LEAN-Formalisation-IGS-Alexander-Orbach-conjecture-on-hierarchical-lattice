import IGSIII34.Spectral.ActualTypicalMassCompletion20261011
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology

/-- Two-sided subexponential Perron bounds imply the logarithmic mass
asymptotic. In the actual application the lower bound comes from mass
sampling, rather than a negative moment of the continuation mass. -/
theorem logarithmic_mass_limit_of_subexponential_bounds
    (mass : ℕ → ℝ) (radius : ℝ) (radiusPositive : 0 < radius)
    (massPositive : ∀ depth, 0 < mass depth)
    (bounds : ∀ growth : ℝ, 1 < growth → ∃ coefficient : ℝ,
      0 < coefficient ∧ ∃ threshold : ℕ, ∀ depth, threshold ≤ depth →
        (growth ^ depth)⁻¹ < mass depth * radius ^ depth ∧
        mass depth * radius ^ depth ≤ coefficient * growth ^ depth) :
    Tendsto (fun depth => Real.log (mass depth) / depth) atTop (𝓝 (-Real.log radius)) := by
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerancePositive
  have growthAboveOne : 1 < Real.exp (tolerance / 2) :=
    Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨coefficient, coefficientPositive, threshold, estimates⟩ :=
    bounds (Real.exp (tolerance / 2)) growthAboveOne
  have coefficientDecay := (tendsto_const_div_atTop_nhds_zero_nat
    (Real.log coefficient)).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < tolerance / 2))
  obtain ⟨coefficientThreshold, coefficientEstimates⟩ := eventually_atTop.mp coefficientDecay
  refine ⟨max 1 (max threshold coefficientThreshold), ?_⟩
  intro depth after
  have depthPositive : 0 < (depth : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) ((le_max_left _ _).trans after))
  have actualBounds := estimates depth
    ((le_max_left threshold coefficientThreshold).trans ((le_max_right _ _).trans after))
  have coefficientSmall := coefficientEstimates depth
    ((le_max_right threshold coefficientThreshold).trans ((le_max_right _ _).trans after))
  have lowerLog := Real.log_lt_log (inv_pos.mpr (pow_pos (Real.exp_pos _) depth)) actualBounds.1
  have upperLog := Real.log_le_log (mul_pos (massPositive depth) (pow_pos radiusPositive depth)) actualBounds.2
  rw [Real.log_inv, Real.log_pow, Real.log_exp,
    Real.log_mul (massPositive depth).ne' (pow_pos radiusPositive depth).ne', Real.log_pow] at lowerLog
  rw [Real.log_mul (massPositive depth).ne' (pow_pos radiusPositive depth).ne', Real.log_pow,
    Real.log_mul coefficientPositive.ne' (pow_pos (Real.exp_pos _) depth).ne',
    Real.log_pow, Real.log_exp] at upperLog
  have lowerDiv := (div_lt_div_iff_of_pos_right depthPositive).mpr lowerLog
  have upperDiv := (div_le_div_iff_of_pos_right depthPositive).mpr upperLog
  have normalization : (Real.log (mass depth) + (depth : ℝ) * Real.log radius) / depth =
      Real.log (mass depth) / depth + Real.log radius := by field_simp
  rw [normalization] at lowerDiv upperDiv
  have lowerEquality : (-((depth : ℝ) * (tolerance / 2))) / depth = -(tolerance / 2) := by field_simp
  have upperEquality : (Real.log coefficient + (depth : ℝ) * (tolerance / 2)) / depth =
      Real.log coefficient / depth + tolerance / 2 := by field_simp
  rw [lowerEquality] at lowerDiv
  rw [upperEquality] at upperDiv
  rw [Real.dist_eq, sub_neg_eq_add, abs_lt]
  constructor <;> linarith

end
end IGSIII34.Spectral

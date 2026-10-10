import IGSIII.Mass.ShortestRouteBound
import IGSIII.Chemical.SubstitutionPaths.FiveCycleGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall Matrix

theorem chemical_dimension_exponent_le_ambient (massGrowth ambientGrowth chemicalGrowth : ℝ)
    (massAtLeastOne : 1 ≤ massGrowth) (ambientGreaterThanOne : 1 < ambientGrowth)
    (growthBound : ambientGrowth ≤ chemicalGrowth) :
    Real.log massGrowth / Real.log chemicalGrowth ≤ Real.log massGrowth / Real.log ambientGrowth := by
  exact div_le_div_of_nonneg_left (Real.log_nonneg massAtLeastOne)
    (Real.log_pos ambientGreaterThanOne)
    (Real.log_le_log (zero_lt_one.trans ambientGreaterThanOne) growthBound)

theorem chemical_dimension_exponent_lt_ambient (massGrowth ambientGrowth chemicalGrowth : ℝ)
    (massGreaterThanOne : 1 < massGrowth) (ambientGreaterThanOne : 1 < ambientGrowth)
    (growthBound : ambientGrowth < chemicalGrowth) :
    Real.log massGrowth / Real.log chemicalGrowth < Real.log massGrowth / Real.log ambientGrowth := by
  exact div_lt_div_of_pos_left (Real.log_pos massGreaterThanOne)
    (Real.log_pos ambientGreaterThanOne)
    (Real.log_lt_log (zero_lt_one.trans ambientGreaterThanOne) growthBound)

/-- The comparison uses the actual full-cluster Perron root. It makes no
identification of the expected ambient mass exponent with an almost-sure
ambient Hausdorff dimension. -/
theorem actual_chemical_dimension_exponent_le_ambient
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthLower : (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth) :
    Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth ≤
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
  have ambientGreaterThanOne : (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
    exact_mod_cast classicalRule.scale
  exact chemical_dimension_exponent_le_ambient _ _ _
    (ambientGreaterThanOne.le.trans (classicalRule.distance_le_mass_spectralRadius p positive belowOne fixedPoint))
    ambientGreaterThanOne growthLower

/-- For the genuine five-cycle rule the chemical exponent is strictly below
the ambient expected mass exponent, for every growth satisfying its actual
mean upper bounds. -/
theorem actual_five_cycle_dimension_exponent_strict
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : IGSIII.Chemical.FiveCycle.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanUpper : ∀ depth, conditionedDistanceMean (IGSIII.Chemical.FiveCycle.rule.generation depth).network p ≤
      constant⁻¹ * growth ^ (depth + 1)) :
    Real.log ((spectralRadius ℂ ((IGSIII.Chemical.FiveCycle.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth <
      Real.log ((spectralRadius ℂ ((IGSIII.Chemical.FiveCycle.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log 2 := by
  have massBound := IGSIII.Chemical.FiveCycle.rule_classical.distance_le_mass_spectralRadius p positive belowOne fixedPoint
  change (IGSIII.Chemical.FiveCycle.network.fullGraph.dist IGSIII.Chemical.FiveCycle.network.source
    IGSIII.Chemical.FiveCycle.network.target : ℝ) ≤ _ at massBound
  rw [IGSIII.Chemical.FiveCycle.terminal_distance] at massBound
  have growthBound := (IGSIII.Chemical.FiveCycle.actual_growth_lower_bound p positive belowOne fixedPoint
    constant growth growthPositive meanUpper).2
  exact chemical_dimension_exponent_lt_ambient _ 2 growth (by exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) massBound)
    (by norm_num) growthBound

end
end IGSIII.Geometry



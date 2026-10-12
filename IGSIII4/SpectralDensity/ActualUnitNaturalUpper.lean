import IGSIII4.SpectralDensity.ActualUnitInputUpper
import IGSIII4.SpectralDensity.NaturalGrowthTransfer
import IGSIII4.SpectralDensity.ActualDensityLimit
import IGSIII34.Percolation.GenerationMean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Probability Filter Topology
open scoped BigOperators

theorem weightedCell_unit_mean_eq_conditional_mean {Outcome : Type*} [Fintype Outcome]
    (blocks paths interior : ℕ) (probability : ℝ) (weight : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) :
    weightedCellMean blocks paths interior probability weight (fun _ => 1) =
      conditionalMeanResistance (network blocks paths interior) probability := by
  unfold weightedCellMean weightedCellObservable
  simp only [id_eq]
  simp_rw [finiteMean_const _ (sum_productWeight weight normalized)]
  exact finiteMean_conditional_unitResistance _ _

theorem actual_natural_growth_le_weighted_unit_mean {Outcome : Type*} [Fintype Outcome]
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : (network blocks paths interior).reliability probability = probability)
    (natural : NaturalResistanceCompletion (rule blocks paths interior) probability positive belowOne fixedPoint)
    (weight : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) :
    natural.growth ≤ weightedCellMean blocks paths interior probability weight (fun _ => 1) := by
  rw [weightedCell_unit_mean_eq_conditional_mean blocks paths interior probability weight normalized]
  have upper := actual_natural_growth_le_unit_mean (rule blocks paths interior)
    (classical blocks paths interior pathsPositive) probability positive belowOne fixedPoint natural
  rw [electricalOrbitScale_succ_eq_generation_mean (rule blocks paths interior)
    (classical blocks paths interior pathsPositive) probability positive belowOne fixedPoint 0] at upper
  exact upper

/-- The actual natural resistance multiplier satisfies the manuscript's upper
bound, with no electrical estimate supplied as a premise. -/
theorem appendix_actual_natural_growth_upper (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      (appendixNaturalCompletion base length).growth ≤
        (2 + 8 / Real.log base) * (blockCount base length : ℝ) := by
  have unitUpper := appendix_weightedCell_unit_mean_upper base baseAboveOne
    (fun _ : Unit => (1 : ℝ)) (fun _ => by norm_num) (by simp)
  filter_upwards [unitUpper, eventually_ge_atTop (2 : ℕ)] with length upper lengthLarge
  have pathsPositive : 0 < pathCount (max length 2) := Nat.ceil_pos.mpr (by
    have : (0 : ℝ) < (max length 2 : ℕ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_max_right length 2))
    positivity : 0 < ((max length 2 : ℕ) : ℝ) * (4 / 3 : ℝ) ^ max length 2)
  have bound := actual_natural_growth_le_weighted_unit_mean
    (blockCount base (max length 2)) (pathCount (max length 2)) (max length 2 - 2) pathsPositive
    (appendixCriticalProbability base (max length 2))
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.1
    (appendixCriticalProbability_spec base _ (Nat.le_max_right _ _)).2.2
    (appendixNaturalCompletion base length) (fun _ : Unit => (1 : ℝ)) (by simp)
  apply bound.trans
  simpa only [max_eq_left lengthLarge] using upper

end
end IGSIII4.SpectralDensity.ActualFamily

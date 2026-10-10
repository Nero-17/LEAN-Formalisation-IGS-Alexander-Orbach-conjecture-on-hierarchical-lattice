import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

def positiveFiniteApprox (index : ℕ) : SimpleFunc ℝ≥0 ℝ≥0 :=
  SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ _) index +
    SimpleFunc.const _ (1 / ((index : ℝ≥0) + 1))

theorem positiveFiniteApprox_positive (index : ℕ) (value : ℝ≥0) :
    0 < positiveFiniteApprox index value := by
  change 0 < SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ _) index value +
    1 / ((index : ℝ≥0) + 1)
  exact add_pos_of_nonneg_of_pos zero_le (by positivity)

theorem positiveFiniteApprox_bound (index : ℕ) (value : ℝ≥0) :
    positiveFiniteApprox index value ≤ 2 * value + 1 := by
  have bound := SimpleFunc.edist_approxOn_y0_le (f := id) measurable_id (s := Set.univ)
    (y₀ := (0 : ℝ≥0)) (Set.mem_univ _) value index
  have coefficient : 1 / ((index : ℝ≥0) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (by positivity)
  change SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ _) index value +
    1 / ((index : ℝ≥0) + 1) ≤ _
  have approximationBound : SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ _) index value ≤ 2 * value := by
    have realBound :
        ENNReal.ofReal ((SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ _) index value : ℝ≥0) : ℝ) ≤
          ENNReal.ofReal (2 * (value : ℝ)) := by
      simpa only [edist_dist, NNReal.dist_eq, NNReal.coe_zero, zero_sub, abs_neg, NNReal.abs_eq,
        id_eq, ← ENNReal.ofReal_add (by positivity : 0 ≤ (value : ℝ)), ← two_mul] using bound
    apply NNReal.coe_le_coe.mp
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp realBound
  exact add_le_add approximationBound coefficient

theorem positiveFiniteApprox_tendsto (value : ℝ≥0) :
    Tendsto (fun index => positiveFiniteApprox index value) atTop (𝓝 value) := by
  have approximation := SimpleFunc.tendsto_approxOn (f := id) measurable_id
    (s := Set.univ) (y₀ := (0 : ℝ≥0)) (Set.mem_univ _) (x := value) (by simp)
  have correction : Tendsto (fun index : ℕ => 1 / ((index : ℝ≥0) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  convert approximation.add correction using 1 <;> simp [positiveFiniteApprox]

end
end IGSIII34.Probability

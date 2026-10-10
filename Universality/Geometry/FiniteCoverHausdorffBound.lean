import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality.Geometry
noncomputable section
open Set Filter Metric MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal

/-- Exponentially many shrinking finite covers, with arbitrary finite
prefactors, give zero Hausdorff measure above their logarithmic growth rate. -/
theorem hausdorffMeasure_eq_zero_of_finite_geometric_cover
    {Ambient : Type*} [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Node : ℕ → Type*) [∀ depth, Fintype (Node depth)]
    (set : Set Ambient) (cover : ∀ depth, Node depth → Set Ambient)
    (ratio diameter countConstant : ℝ) (hratio : 0 ≤ ratio) (hratioOne : ratio < 1)
    (hcountConstant : 0 ≤ countConstant) (branching : ℕ)
    (hcard : ∀ depth, (Fintype.card (Node depth) : ℝ) ≤ countConstant * (branching : ℝ) ^ depth)
    (hdiameter : ∀ depth node, ∀ x ∈ cover depth node, ∀ y ∈ cover depth node,
      dist x y ≤ ratio ^ depth * diameter)
    (hcover : ∀ depth, set ⊆ ⋃ node, cover depth node)
    (dimension : ℝ) (hdimension : 0 ≤ dimension)
    (hdecrease : (branching : ℝ≥0∞) * ENNReal.ofReal ratio ^ dimension < 1) :
    Measure.hausdorffMeasure dimension set = 0 := by
  have hshrink : Tendsto (fun depth : ℕ => ENNReal.ofReal (ratio ^ depth * diameter))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.tendsto (0 * diameter) |>.comp
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratioOne).mul_const diameter)
  have hbound (depth : ℕ) :
      (∑ node : Node depth, ediam (cover depth node) ^ dimension) ≤
        ((branching : ℝ≥0∞) * ENNReal.ofReal ratio ^ dimension) ^ depth *
          (ENNReal.ofReal countConstant * ENNReal.ofReal diameter ^ dimension) := by
    have hcount : (Fintype.card (Node depth) : ℝ≥0∞) ≤
        ENNReal.ofReal countConstant * (branching : ℝ≥0∞) ^ depth := by
      have hcast := ENNReal.ofReal_le_ofReal (hcard depth)
      simpa only [ENNReal.ofReal_mul hcountConstant, ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (show (0 : ℝ) ≤ branching by positivity)] using hcast
    calc
      _ ≤ ∑ _node : Node depth, ENNReal.ofReal (ratio ^ depth * diameter) ^ dimension := by
        apply Finset.sum_le_sum
        intro node _
        exact ENNReal.rpow_le_rpow (ediam_le_of_forall_dist_le (hdiameter depth node)) hdimension
      _ = (Fintype.card (Node depth) : ℝ≥0∞) *
          ENNReal.ofReal (ratio ^ depth * diameter) ^ dimension := by simp
      _ ≤ (ENNReal.ofReal countConstant * (branching : ℝ≥0∞) ^ depth) *
          ENNReal.ofReal (ratio ^ depth * diameter) ^ dimension := by
        apply mul_le_mul_left
        exact hcount
      _ = _ := by
        rw [ENNReal.ofReal_mul (pow_nonneg hratio depth), ENNReal.ofReal_pow hratio,
          ENNReal.mul_rpow_of_nonneg _ _ hdimension,
          ← ENNReal.rpow_natCast_mul, mul_comm (depth : ℝ) dimension,
          ENNReal.rpow_mul_natCast, mul_pow]
        ac_rfl
  have hlimit : Tendsto (fun depth : ℕ =>
      ((branching : ℝ≥0∞) * ENNReal.ofReal ratio ^ dimension) ^ depth *
        (ENNReal.ofReal countConstant * ENNReal.ofReal diameter ^ dimension)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hdecrease)
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hdimension ENNReal.ofReal_ne_top)))
  apply le_antisymm _ bot_le
  calc
    _ ≤ liminf (fun depth => ∑ node : Node depth, ediam (cover depth node) ^ dimension) atTop :=
      hausdorffMeasure_le_liminf_sum dimension set _ hshrink cover
        (Eventually.of_forall (fun depth node => ediam_le_of_forall_dist_le (hdiameter depth node)))
        (Eventually.of_forall hcover)
    _ ≤ liminf (fun depth : ℕ =>
        ((branching : ℝ≥0∞) * ENNReal.ofReal ratio ^ dimension) ^ depth *
          (ENNReal.ofReal countConstant * ENNReal.ofReal diameter ^ dimension)) atTop :=
      liminf_le_liminf (Eventually.of_forall hbound)
    _ = 0 := hlimit.liminf_eq

theorem dimH_le_of_finite_geometric_cover
    {Ambient : Type*} [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Node : ℕ → Type*) [∀ depth, Fintype (Node depth)]
    (set : Set Ambient) (cover : ∀ depth, Node depth → Set Ambient)
    (ratio diameter countConstant : ℝ) (hratio : 0 < ratio) (hratioOne : ratio < 1)
    (hcountConstant : 0 ≤ countConstant) (branching : ℕ) (hbranching : 0 < branching)
    (hcard : ∀ depth, (Fintype.card (Node depth) : ℝ) ≤ countConstant * (branching : ℝ) ^ depth)
    (hdiameter : ∀ depth node, ∀ x ∈ cover depth node, ∀ y ∈ cover depth node,
      dist x y ≤ ratio ^ depth * diameter)
    (hcover : ∀ depth, set ⊆ ⋃ node, cover depth node) :
    dimH set ≤ ENNReal.ofReal (Real.log (branching : ℝ) / (-Real.log ratio)) := by
  apply dimH_le
  intro dimension htop
  by_contra hnot
  have hreal : Real.log (branching : ℝ) / (-Real.log ratio) < (dimension : ℝ) := by
    by_contra hle
    apply hnot
    have hle' := ENNReal.ofReal_le_ofReal (le_of_not_gt hle)
    simpa only [ENNReal.ofReal_coe_nnreal] using hle'
  have hratioLog : Real.log ratio < 0 := Real.log_neg hratio hratioOne
  have hlogInequality : Real.log (branching : ℝ) + Real.log ratio * dimension < 0 := by
    have hmul := (div_lt_iff₀ (neg_pos.mpr hratioLog)).mp hreal
    nlinarith
  have hbranchingReal : 0 < (branching : ℝ) := by exact_mod_cast hbranching
  have hdecreaseReal : (branching : ℝ) * ratio ^ (dimension : ℝ) < 1 := by
    calc
      _ = Real.exp (Real.log (branching : ℝ) + Real.log ratio * dimension) := by
        rw [Real.exp_add, Real.exp_log hbranchingReal, Real.rpow_def_of_pos hratio]
      _ < 1 := Real.exp_lt_one_iff.mpr hlogInequality
  have hdecrease : (branching : ℝ≥0∞) * ENNReal.ofReal ratio ^ (dimension : ℝ) < 1 := by
    have h := ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 1 by norm_num) |>.mpr hdecreaseReal
    simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul hbranchingReal.le,
      ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg hratio.le dimension.coe_nonneg] using h
  have hzero := hausdorffMeasure_eq_zero_of_finite_geometric_cover Node set cover
    ratio diameter countConstant hratio.le hratioOne hcountConstant branching hcard hdiameter hcover
    dimension dimension.coe_nonneg hdecrease
  rw [htop] at hzero
  exact ENNReal.top_ne_zero hzero

end
end Universality.Geometry


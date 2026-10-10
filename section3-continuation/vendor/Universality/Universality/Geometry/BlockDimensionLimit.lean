import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Pure analysis for taking the limit of finite-block dimension bounds.
The conclusion also holds without positivity assumptions on the natural
parameters, so the intended branching > 1 and scale > 1 case is included. -/

namespace Universality
noncomputable section
open Filter
open scoped Topology ENNReal

theorem logarithmic_dimension_le_of_block_bounds
    (branching scale overhead : ℕ) (dimension : ℝ≥0∞)
    (hbound : ∀ depth : ℕ, 1 ≤ depth →
      ENNReal.ofReal ((depth : ℝ) * Real.log (branching : ℝ) /
        ((depth + overhead : ℕ) * Real.log (scale : ℝ))) ≤ dimension) :
    ENNReal.ofReal (Real.log (branching : ℝ) / Real.log (scale : ℝ)) ≤ dimension := by
  have hlimit : Tendsto
      (fun depth : ℕ => (depth : ℝ) * Real.log (branching : ℝ) /
        ((depth + overhead : ℕ) * Real.log (scale : ℝ))) atTop
      (𝓝 (Real.log (branching : ℝ) / Real.log (scale : ℝ))) := by
    simpa only [one_mul, div_mul_div_comm, Nat.cast_add] using
      (tendsto_natCast_div_add_atTop (overhead : ℝ)).mul_const
        (Real.log (branching : ℝ) / Real.log (scale : ℝ))
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlimit)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with depth hdepth
  exact hbound depth hdepth

end
end Universality


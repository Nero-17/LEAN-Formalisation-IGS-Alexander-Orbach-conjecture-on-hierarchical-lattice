import Universality.Graph.FiniteVolume
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem generation_volume_ratio (rule : Rule) (n : ℕ) (hedges : 1 < rule.edges) :
    ((rule.generation n).vertices : ℝ) / (rule.edges : ℝ) ^ (n + 1) =
      2 * (1 / (rule.edges : ℝ)) ^ (n + 1) +
        ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1) *
          (1 - (1 / (rule.edges : ℝ)) ^ (n + 1)) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hne : (rule.edges : ℝ) ≠ 0 := (lt_trans zero_lt_one hm).ne'
  have hsub : (rule.edges : ℝ) - 1 ≠ 0 := (sub_pos.mpr hm).ne'
  rw [rule.generation_volume_formula n (by omega)]
  rw [one_div_pow]
  field_simp

theorem generation_volume_ratio_tendsto (rule : Rule) (hedges : 1 < rule.edges) :
    Tendsto (fun n : ℕ => ((rule.generation n).vertices : ℝ) / (rule.edges : ℝ) ^ (n + 1)) atTop
      (𝓝 (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1))) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hp : Tendsto (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (one_div_nonneg.mpr (lt_trans zero_lt_one hm).le)
      ((div_lt_one (lt_trans zero_lt_one hm)).mpr hm)).comp (tendsto_add_atTop_nat 1)
  simp_rw [rule.generation_volume_ratio _ hedges]
  simpa using (hp.const_mul 2).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)))

end
end Universality.Rule

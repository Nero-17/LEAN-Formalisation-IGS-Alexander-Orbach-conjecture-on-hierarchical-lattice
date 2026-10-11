import Universality.Percolation.PostexitSupercriticalBound
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality.Rule
noncomputable section

theorem Classical.postexit_supercritical_birth_sum {rule : Rule} (h : rule.Classical)
    (critical lower : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hlower : critical < lower) (hlower' : lower < 1) (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ p exitParameter : ℝ, 0 < p → p < 1 →
      lower ≤ exitParameter → exitParameter < 1 → ∀ offset : ℕ,
      rule.network.reliability^[offset] p = exitParameter → ∀ scale : ℝ, 1 ≤ scale →
      (∀ state k, k ≤ 2 * order → (rule.generation offset).network.conditionalVertexMoment p state k ≤
        scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) →
      Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ n *
        rule.expectedClusterBirthPower p order (offset + n + 1)) ∧
      (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ n *
        rule.expectedClusterBirthPower p order (offset + n + 1)) ≤ bound * scale ^ order := by
  obtain ⟨constant, hconstant, hb⟩ := h.postexit_supercritical_birth_bound
    critical lower hc hc' hfixed hlower hlower' order horder
  have hm : (1 : ℝ) ≤ rule.edges := by have := h.edges_gt_one; exact_mod_cast (by omega : 1 ≤ rule.edges)
  have hmpos : (0 : ℝ) < rule.edges := zero_lt_one.trans_le hm
  have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨2 * constant, by positivity, ?_⟩
  intro p exitParameter hp hp' hexit hexit' offset hparameter scale hscale hbase
  have hmajor := hs.mul_left (constant * scale ^ order)
  have hnonneg (n : ℕ) : 0 ≤ (1 / (rule.edges : ℝ)) ^ n *
      rule.expectedClusterBirthPower p order (offset + n + 1) :=
    mul_nonneg (pow_nonneg (one_div_nonneg.mpr hmpos.le) _)
      (rule.expectedClusterBirthPower_nonneg hp.le hp'.le _ _)
  have hbound (n : ℕ) : (1 / (rule.edges : ℝ)) ^ n *
      rule.expectedClusterBirthPower p order (offset + n + 1) ≤ (constant * scale ^ order) * (1 / 2 : ℝ) ^ n := by
    calc
      _ ≤ rule.expectedClusterBirthPower p order (offset + n + 1) :=
        mul_le_of_le_one_left (rule.expectedClusterBirthPower_nonneg hp.le hp'.le _ _)
          (pow_le_one₀ (one_div_nonneg.mpr hmpos.le) ((div_le_one hmpos).mpr hm))
      _ ≤ _ := hb p exitParameter hp hp' hexit hexit' offset hparameter scale hscale hbase n
  have hsum := hmajor.of_nonneg_of_le hnonneg hbound
  refine ⟨hsum, (hsum.tsum_le_tsum hbound hmajor).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
  ring

end
end Universality.Rule

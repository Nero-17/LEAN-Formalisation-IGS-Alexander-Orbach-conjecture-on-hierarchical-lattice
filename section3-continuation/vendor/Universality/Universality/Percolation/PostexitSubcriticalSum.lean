import Universality.Percolation.PostexitSubcriticalBound
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality.Rule
noncomputable section

theorem Classical.postexit_subcritical_birth_sum {rule : Rule} (h : rule.Classical)
    (critical upperParameter : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hu : 0 < upperParameter)
    (huc : upperParameter < critical) (order : ℕ) (horder : 1 ≤ order)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ order < rule.edges) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ p exitParameter : ℝ, 0 < p → p < 1 →
      0 < exitParameter → exitParameter ≤ upperParameter → ∀ offset : ℕ,
      rule.network.reliability^[offset] p = exitParameter → ∀ scale : ℝ, 1 ≤ scale →
      (∀ state k, k ≤ order → (rule.generation offset).network.conditionalVertexMoment p state k ≤
        scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) →
      Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ n *
        rule.expectedClusterBirthPower p order (offset + n + 1)) ∧
      (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ n *
        rule.expectedClusterBirthPower p order (offset + n + 1)) ≤ bound * scale ^ order := by
  obtain ⟨constant, hconstant, hb⟩ := h.postexit_subcritical_birth_bound
    critical upperParameter hc hc' hfixed hu huc order horder
  have hm : (0 : ℝ) < rule.edges := by have := h.edges_gt_one; exact_mod_cast (by omega : 0 < rule.edges)
  let ratio : ℝ := (rule.network.fullGraph.degree rule.network.source : ℝ) ^ order / rule.edges
  have hratio : 0 ≤ ratio := div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hm.le
  have hratio' : ratio < 1 := (div_lt_one hm).mpr hthreshold
  have hs := summable_geometric_of_lt_one hratio hratio'
  refine ⟨constant / (1 - ratio), div_pos hconstant (sub_pos.mpr hratio'), ?_⟩
  intro p exitParameter hp hp' hexit hexitUpper offset hparameter scale hscale hbase
  have hmajor := hs.mul_left (constant * scale ^ order)
  have hnonneg (n : ℕ) : 0 ≤ (1 / (rule.edges : ℝ)) ^ n *
      rule.expectedClusterBirthPower p order (offset + n + 1) :=
    mul_nonneg (pow_nonneg (one_div_nonneg.mpr hm.le) _)
      (rule.expectedClusterBirthPower_nonneg hp.le hp'.le _ _)
  have hbound (n : ℕ) : (1 / (rule.edges : ℝ)) ^ n *
      rule.expectedClusterBirthPower p order (offset + n + 1) ≤ (constant * scale ^ order) * ratio ^ n := by
    have hh := mul_le_mul_of_nonneg_left
      (hb p exitParameter hp hp' hexit hexitUpper offset hparameter scale hscale hbase n)
      (pow_nonneg (one_div_nonneg.mpr hm.le) n)
    calc
      _ ≤ (1 / (rule.edges : ℝ)) ^ n * (constant * scale ^ order *
          (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n)) := hh
      _ = (constant * scale ^ order) * ratio ^ n := by
        dsimp [ratio]
        simp only [div_pow, one_pow, pow_mul]
        ring
  have hsum := hmajor.of_nonneg_of_le hnonneg hbound
  refine ⟨hsum, (hsum.tsum_le_tsum hbound hmajor).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hratio hratio']
  ring

end
end Universality.Rule

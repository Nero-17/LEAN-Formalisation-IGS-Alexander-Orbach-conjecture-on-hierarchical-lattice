import Universality.Percolation.PostexitVolumeBirth
import Universality.Percolation.SupercriticalBirthSquare
import Universality.Percolation.SupercriticalUniformFailure

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0

/-- True birth moments after supercritical exit have a uniform geometric
tail, on the original critical scale. The doubled initial order enters
only through Cauchy--Schwarz on the event that a child fails to cross. -/
theorem Classical.postexit_supercritical_birth_bound {rule : Rule} (h : rule.Classical)
    (critical lower : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hlower : critical < lower) (hlower' : lower < 1) (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ p exitParameter : ℝ, 0 < p → p < 1 →
      lower ≤ exitParameter → exitParameter < 1 → ∀ offset : ℕ,
      rule.network.reliability^[offset] p = exitParameter → ∀ scale : ℝ, 1 ≤ scale →
      (∀ state k, k ≤ 2 * order → (rule.generation offset).network.conditionalVertexMoment p state k ≤
        scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) → ∀ n : ℕ,
        rule.expectedClusterBirthPower p order (offset + n + 1) ≤
          bound * scale ^ order * (1 / 2 : ℝ) ^ n := by
  have hm : (0 : ℝ) < rule.edges := by have := h.edges_gt_one; exact_mod_cast (by omega : 0 < rule.edges)
  have hv : (0 : ℝ) < rule.vertices := by have := h.vertices_gt_two; exact_mod_cast (by omega : 0 < rule.vertices)
  obtain ⟨constant, hconstant, hb⟩ := h.postexit_birth_volume_bound (2 * order) (by omega)
  obtain ⟨failure, hfailure, hf⟩ := h.supercritical_uniform_failure_bound critical lower
    (4 * (rule.edges : ℝ) ^ (2 * order)) hc hc' hfixed hlower hlower'.le (by positivity)
  let coefficient : ℝ := (rule.vertices : ℝ) * rule.edges * constant * failure
  have hcoefficient : 0 < coefficient := by dsimp [coefficient]; positivity
  refine ⟨1 + coefficient, by positivity, ?_⟩
  intro p exitParameter hp hp' hexit hexit' offset hparameter scale hscale hbase n
  have hexitPos : 0 < exitParameter := (hc.trans hlower).trans_le hexit
  have hcrossing : (rule.generation (offset + n)).network.reliability p =
      (rule.generation n).network.reliability exitParameter := by
    rw [rule.generation_reliability_iterate, rule.generation_reliability_iterate, ← hparameter,
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hsquare := rule.network.expectedBirthClusterPower_square_le_failure
    (rule.generation (offset + n)).network h.connected hp.le hp'.le order
  change rule.expectedClusterBirthPower p order (offset + n + 1) ^ 2 ≤
    (rule.vertices : ℝ) * ((rule.edges : ℝ) * (1 - (rule.generation (offset + n)).network.reliability p)) *
      rule.expectedClusterBirthPower p (2 * order) (offset + n + 1) at hsquare
  rw [hcrossing] at hsquare
  have hvolume := hb p exitParameter hp hp' hexitPos hexit' offset hparameter scale hscale hbase n
  have hfailNonneg : 0 ≤ 1 - (rule.generation n).network.reliability exitParameter :=
    sub_nonneg.mpr ((rule.generation n).network.reliability_le_one hexitPos.le hexit'.le)
  have hfail := hf exitParameter hexit hexit'.le n
  have hdecay : (rule.edges : ℝ) ^ (2 * order * n) *
      (1 - (rule.generation n).network.reliability exitParameter) ≤ failure * (1 / 4 : ℝ) ^ n := by
    have hcancel : (4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((4 * (rule.edges : ℝ) ^ (2 * order)) ^ n *
          (1 - (rule.generation n).network.reliability exitParameter)) * (1 / 4 : ℝ) ^ n := by
        rw [mul_pow, ← pow_mul]
        calc
          _ = ((4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) *
              ((rule.edges : ℝ) ^ (2 * order * n) * (1 - (rule.generation n).network.reliability exitParameter)) := by rw [hcancel, one_mul]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfail (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n)
  have hmain : rule.expectedClusterBirthPower p order (offset + n + 1) ^ 2 ≤
      coefficient * scale ^ (2 * order) * (1 / 4 : ℝ) ^ n := by
    calc
      _ ≤ (rule.vertices : ℝ) * ((rule.edges : ℝ) * (1 - (rule.generation n).network.reliability exitParameter)) *
          (constant * scale ^ (2 * order) * (rule.edges : ℝ) ^ (2 * order * n)) :=
        hsquare.trans (mul_le_mul_of_nonneg_left hvolume (mul_nonneg hv.le (mul_nonneg hm.le hfailNonneg)))
      _ = ((rule.vertices : ℝ) * rule.edges * constant * scale ^ (2 * order)) *
          ((rule.edges : ℝ) ^ (2 * order * n) * (1 - (rule.generation n).network.reliability exitParameter)) := by ring
      _ ≤ ((rule.vertices : ℝ) * rule.edges * constant * scale ^ (2 * order)) * (failure * (1 / 4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = _ := by dsimp [coefficient]; ring
  apply (sq_le_sq₀ (rule.expectedClusterBirthPower_nonneg hp.le hp'.le _ _)
    (by positivity : 0 ≤ (1 + coefficient) * scale ^ order * (1 / 2 : ℝ) ^ n)).mp
  calc
    _ ≤ coefficient * scale ^ (2 * order) * (1 / 4 : ℝ) ^ n := hmain
    _ ≤ (1 + coefficient) ^ 2 * scale ^ (2 * order) * (1 / 4 : ℝ) ^ n := by
      gcongr
      nlinarith [sq_nonneg coefficient]
    _ = _ := by
      have hscalePower : scale ^ (2 * order) = (scale ^ order) ^ 2 := by rw [← pow_mul, Nat.mul_comm order 2]
      have hhalfPower : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
        rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
        norm_num
      rw [hscalePower, hhalfPower]
      ring

end
end Universality.Rule

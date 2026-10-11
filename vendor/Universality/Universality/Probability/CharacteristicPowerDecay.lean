import Universality.Probability.L2Characteristic
import Mathlib.Analysis.SpecificLimits.Normed

namespace Universality
noncomputable section
open Filter
open scoped Topology

/-- Iterated offspring powers beat every fixed geometric weight. This supplies
all polynomially weighted Fourier integrability without logarithmic exponents. -/
theorem summable_geometric_mul_iterated_power (bound geometric : ℝ) (degree : ℕ)
    (hbound0 : 0 ≤ bound) (hbound1 : bound < 1)
    (hgeometric : 0 < geometric) (hdegree : 2 ≤ degree) :
    Summable (fun n : ℕ => bound ^ (degree ^ n) * geometric ^ n) := by
  by_cases hzero : bound = 0
  · subst bound
    have hd : degree ≠ 0 := by omega
    simpa only [zero_pow (pow_ne_zero _ hd), zero_mul] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hbound : 0 < bound := lt_of_le_of_ne hbound0 (Ne.symm hzero)
  let sequence (n : ℕ) := bound ^ (degree ^ n) * geometric ^ n
  have hpositive (n : ℕ) : 0 < sequence n := mul_pos (pow_pos hbound _) (pow_pos hgeometric _)
  have hpower : Tendsto (fun n : ℕ => bound ^ (degree ^ n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hbound0 hbound1).comp
      (tendsto_pow_atTop_atTop_of_one_lt (show 1 < degree by omega))
  have hfactor (n : ℕ) : sequence (n + 1) = sequence n * (bound ^ (degree ^ n)) ^ (degree - 1) * geometric := by
    dsimp [sequence]
    rw [show degree ^ (n + 1) = degree ^ n * degree by rw [pow_succ], pow_mul]
    rw [show geometric ^ (n + 1) = geometric ^ n * geometric by rw [pow_succ]]
    have hexponent : (bound ^ (degree ^ n)) ^ degree =
        (bound ^ (degree ^ n)) ^ (degree - 1 + 1) := by
      rw [Nat.sub_add_cancel (show 1 ≤ degree by omega)]
    rw [hexponent, pow_succ]
    ring
  have hratio (n : ℕ) : ‖sequence (n + 1)‖ / ‖sequence n‖ =
      (bound ^ (degree ^ n)) ^ (degree - 1) * geometric := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hpositive _), abs_of_pos (hpositive _), hfactor]
    field_simp [(hpositive n).ne']
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
    (Eventually.of_forall (fun n => (hpositive n).ne'))
  simp_rw [hratio]
  have hnonzero : degree - 1 ≠ 0 := by omega
  simpa only [zero_pow hnonzero, zero_mul] using (hpower.pow (degree - 1)).mul_const geometric

end
end Universality

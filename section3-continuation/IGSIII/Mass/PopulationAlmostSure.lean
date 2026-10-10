import IGSIII.Mass.GeometricReward
import Universality.Probability.SubcriticalL2Recursion

set_option autoImplicit false

namespace IGSIII.Mass

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {probability : Measure Ω}

theorem ae_normalized_sum_zero_of_geometric_bound
    (population : ℕ → Ω → ℝ) (square_integrable : ∀ n, MemLp (population n) 2 probability)
    (bound rate radius : ℝ) (bound_nonnegative : 0 ≤ bound)
    (rate_gt_one : 1 < rate) (rate_lt_radius : rate < radius)
    (estimate : ∀ n, eLpNorm (population n) 2 probability ≤ ENNReal.ofReal (bound * rate ^ n)) :
    ∀ᵐ sample ∂probability,
      Tendsto (fun n => (∑ k ∈ Finset.range n, population k sample) / radius ^ n) atTop (𝓝 0) := by
  have rate_positive : 0 < rate := zero_lt_one.trans rate_gt_one
  have radius_positive : 0 < radius := rate_positive.trans rate_lt_radius
  have sum_bound (n : ℕ) : eLpNorm (∑ k ∈ Finset.range n, population k) 2 probability ≤
      ENNReal.ofReal (bound * (rate ^ n / (rate - 1))) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, eLpNorm (population k) 2 probability :=
        eLpNorm_sum_le (fun k _ => (square_integrable k).aestronglyMeasurable) (by norm_num)
      _ ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (bound * rate ^ k) :=
        Finset.sum_le_sum (fun k _ => estimate k)
      _ = ENNReal.ofReal (bound * ∑ k ∈ Finset.range n, rate ^ k) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
          mul_nonneg bound_nonnegative (pow_nonneg rate_positive.le k)), Finset.mul_sum]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ bound_nonnegative
        apply (le_div_iff₀ (sub_pos.mpr rate_gt_one)).mpr
        rw [geom_sum_mul]
        linarith
  apply ae_tendsto_zero_of_geometric_L2
    (fun n sample => (∑ k ∈ Finset.range n, population k sample) / radius ^ n)
    (fun n => (Universality.memLp_div_const_real
      (memLp_finsetSum _ (fun k _ => square_integrable k)) _).aestronglyMeasurable)
    (bound / (rate - 1)) (rate / radius)
    (div_nonneg bound_nonnegative (sub_pos.mpr rate_gt_one).le)
    (div_nonneg rate_positive.le radius_positive.le)
    ((div_lt_one radius_positive).mpr rate_lt_radius)
  intro n
  have normalized_eq : (fun sample => (∑ k ∈ Finset.range n, population k sample) / radius ^ n) =
      (radius ^ n)⁻¹ • (∑ k ∈ Finset.range n, population k) := by
    funext sample
    simp [div_eq_mul_inv, mul_comm]
  rw [normalized_eq, eLpNorm_const_smul,
    Real.enorm_of_nonneg (inv_nonneg.mpr (pow_nonneg radius_positive.le n))]
  apply (mul_le_mul_right (sum_bound n) _).trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg radius_positive.le n))]
  congr 1
  rw [div_pow]
  ring

/-- The actual second-moment innovation bound controls a subcritical
eigenpopulation's accumulated reward along the whole sequence almost surely. -/
theorem ae_subcritical_recursion_sum_zero
    (population : ℕ → Ω → ℝ) (square_integrable : ∀ n, MemLp (population n) 2 probability)
    (eigenvalue bound radius : ℝ) (bound_nonnegative : 0 ≤ bound) (radius_gt_one : 1 < radius)
    (spectral_gap : |eigenvalue| < radius)
    (innovation_bound : ∀ n, ∫ sample, (population (n + 1) sample - eigenvalue * population n sample) ^ 2
      ∂probability ≤ bound * radius ^ n) :
    ∀ᵐ sample ∂probability,
      Tendsto (fun n => (∑ k ∈ Finset.range n, population k sample) / radius ^ n) atTop (𝓝 0) := by
  obtain ⟨constant, comparison, constant_nonnegative, comparison_nonnegative, comparison_lt_radius, estimate⟩ :=
    Universality.subcritical_L2_recursion_geometric_bound population square_integrable
      eigenvalue bound radius bound_nonnegative radius_gt_one spectral_gap innovation_bound
  apply ae_normalized_sum_zero_of_geometric_bound population square_integrable constant
    (max comparison ((radius + 1) / 2)) radius constant_nonnegative
    (lt_max_of_lt_right (by linarith))
    (max_lt comparison_lt_radius (by linarith))
  intro n
  apply (estimate n).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ comparison_nonnegative (le_max_left _ _) n) constant_nonnegative

/-- The Perron population's accumulated reward and its terminal population
have the same normalized limit, almost surely. -/
theorem ae_perron_sum_remainder_zero
    (population : ℕ → Ω → ℝ) (square_integrable : ∀ n, MemLp (population n) 2 probability)
    (bound radius : ℝ) (bound_nonnegative : 0 ≤ bound) (radius_gt_one : 1 < radius)
    (innovation_bound : ∀ n, ∫ sample, (population (n + 1) sample - radius * population n sample) ^ 2
      ∂probability ≤ bound * radius ^ n) :
    ∀ᵐ sample ∂probability, Tendsto (fun n =>
      ((∑ k ∈ Finset.range n, population k sample) - population n sample / (radius - 1)) / radius ^ n)
      atTop (𝓝 0) := by
  have innovation_mem (n : ℕ) :
      MemLp (fun sample => population (n + 1) sample - radius * population n sample) 2 probability :=
    (square_integrable (n + 1)).sub ((square_integrable n).const_smul radius)
  have compensation := ae_normalized_sum_zero_of_second_moment_bound
    (fun n sample => population (n + 1) sample - radius * population n sample)
    innovation_mem bound radius bound_nonnegative radius_gt_one innovation_bound
  filter_upwards [compensation] with sample convergence
  have initial : Tendsto (fun n => population 0 sample / radius ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (show |radius⁻¹| < 1 by
          rw [abs_of_pos (inv_pos.mpr (zero_lt_one.trans radius_gt_one))]
          exact inv_lt_one_of_one_lt₀ radius_gt_one)).const_mul (population 0 sample)
  have combined := (initial.add convergence).const_mul (-(radius - 1)⁻¹)
  simp only [add_zero, mul_zero] at combined
  convert combined using 1
  ext n
  have telescoping : (∑ k ∈ Finset.range n, (population (k + 1) sample - radius * population k sample)) =
      population n sample - population 0 sample - (radius - 1) * ∑ k ∈ Finset.range n, population k sample := by
    have expand (k : ℕ) : population (k + 1) sample - radius * population k sample =
        (population (k + 1) sample - population k sample) - (radius - 1) * population k sample := by ring
    simp_rw [expand]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => population k sample) n, ← Finset.mul_sum]
  rw [telescoping]
  field_simp [(sub_pos.mpr radius_gt_one).ne', (zero_lt_one.trans radius_gt_one).ne']
  ring

end IGSIII.Mass

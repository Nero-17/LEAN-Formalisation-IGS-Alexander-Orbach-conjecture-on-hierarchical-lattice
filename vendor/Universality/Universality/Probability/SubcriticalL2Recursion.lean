import Universality.Probability.GeometricL2Sum

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem L2_recursion_geometric_bound (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (eigenvalue bound rate comparison constant : ℝ)
    (hbound : 0 ≤ bound) (hrate : 0 ≤ rate) (hcomparison : 0 ≤ comparison)
    (hrate_le : rate ≤ comparison) (hconstant : 0 ≤ constant)
    (hbudget : bound ≤ constant * (comparison - |eigenvalue|))
    (hzero : eLpNorm (f 0) 2 μ ≤ ENNReal.ofReal constant)
    (hnoise : ∀ n, eLpNorm (f (n + 1) - eigenvalue • f n) 2 μ ≤
      ENNReal.ofReal (bound * rate ^ n)) :
    ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (constant * comparison ^ n) := by
  intro n
  induction n with
  | zero => simpa only [pow_zero, mul_one] using hzero
  | succ n ih =>
    have heq : f (n + 1) = (f (n + 1) - eigenvalue • f n) + eigenvalue • f n := by module
    have hreal : bound * rate ^ n + |eigenvalue| * (constant * comparison ^ n) ≤
        constant * comparison ^ (n + 1) := by
      have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrate hrate_le n) hbound
      have hscaled := mul_le_mul_of_nonneg_right hbudget (pow_nonneg hcomparison n)
      rw [pow_succ]
      nlinarith
    calc
      _ ≤ eLpNorm (f (n + 1) - eigenvalue • f n) 2 μ + eLpNorm (eigenvalue • f n) 2 μ := by
        conv_lhs => rw [heq]
        exact eLpNorm_add_le ((hf (n + 1)).sub ((hf n).const_smul eigenvalue)).aestronglyMeasurable
          ((hf n).const_smul eigenvalue).aestronglyMeasurable (by norm_num)
      _ ≤ ENNReal.ofReal (bound * rate ^ n) +
          ENNReal.ofReal |eigenvalue| * ENNReal.ofReal (constant * comparison ^ n) := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
        exact add_le_add (hnoise n) (mul_le_mul_left' ih _)
      _ = ENNReal.ofReal (bound * rate ^ n + |eigenvalue| * (constant * comparison ^ n)) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_add (mul_nonneg hbound (pow_nonneg hrate n))]
        exact mul_nonneg (abs_nonneg _) (mul_nonneg hconstant (pow_nonneg hcomparison n))
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem L2_normalized_geometric_bound_zero (f : ℕ → Ω → ℝ)
    (constant comparison radius : ℝ) (hcomparison : 0 ≤ comparison) (hradius : 0 < radius)
    (hgap : comparison < radius)
    (hbound : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (constant * comparison ^ n)) :
    Tendsto (fun n => eLpNorm (fun x => f n x / radius ^ n) 2 μ) atTop (𝓝 0) := by
  have hratio : |comparison / radius| < 1 := by
    rw [abs_of_nonneg (div_nonneg hcomparison hradius.le)]
    exact (div_lt_one hradius).mpr hgap
  have hlimit := (ENNReal.continuous_ofReal.tendsto (constant * 0)).comp
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio).const_mul constant)
  simp only [mul_zero, ENNReal.ofReal_zero] at hlimit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimit (fun _ => bot_le)
  intro n
  change eLpNorm (fun x => f n x / radius ^ n) 2 μ ≤ ENNReal.ofReal (constant * (comparison / radius) ^ n)
  have heq : (fun x => f n x / radius ^ n) = (radius ^ n)⁻¹ • f n := by
    funext x
    simp [div_eq_mul_inv, mul_comm]
  rw [heq, eLpNorm_const_smul, Real.enorm_of_nonneg (inv_nonneg.mpr (pow_nonneg hradius.le n))]
  apply (mul_le_mul_left' (hbound n) _).trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hradius.le n))]
  congr 1
  rw [div_pow]
  ring

theorem subcritical_L2_recursion_geometric_bound (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (eigenvalue bound radius : ℝ) (hbound : 0 ≤ bound) (hradius : 1 < radius)
    (heigenvalue : |eigenvalue| < radius)
    (hnoise : ∀ n, ∫ x, (f (n + 1) x - eigenvalue * f n x) ^ 2 ∂μ ≤ bound * radius ^ n) :
    ∃ constant comparison : ℝ, 0 ≤ constant ∧ 0 ≤ comparison ∧ comparison < radius ∧
      ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (constant * comparison ^ n) := by
  have hradius_pos : 0 < radius := lt_trans zero_lt_one hradius
  have hsqrt : Real.sqrt radius < radius := by
    nlinarith [Real.sq_sqrt hradius_pos.le, Real.sqrt_nonneg radius]
  obtain ⟨comparison, hcomparison, hgap⟩ := exists_between (max_lt heigenvalue hsqrt)
  have heigen_comparison : |eigenvalue| < comparison := (le_max_left _ _).trans_lt hcomparison
  have hrate_comparison : Real.sqrt radius < comparison := (le_max_right _ _).trans_lt hcomparison
  have hcomparison_pos : 0 < comparison := (Real.sqrt_pos.mpr hradius_pos).trans hrate_comparison
  have hdenom : 0 < comparison - |eigenvalue| := sub_pos.mpr heigen_comparison
  let constant := (eLpNorm (f 0) 2 μ).toReal + Real.sqrt bound / (comparison - |eigenvalue|)
  have hconstant : 0 ≤ constant := add_nonneg ENNReal.toReal_nonneg
    (div_nonneg (Real.sqrt_nonneg _) hdenom.le)
  have hzero : eLpNorm (f 0) 2 μ ≤ ENNReal.ofReal constant := by
    calc
      _ = ENNReal.ofReal (eLpNorm (f 0) 2 μ).toReal := (ENNReal.ofReal_toReal (hf 0).eLpNorm_lt_top.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hdenom.le))
  have hbudget : Real.sqrt bound ≤ constant * (comparison - |eigenvalue|) :=
    (div_le_iff₀ hdenom).mp (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  refine ⟨constant, comparison, hconstant, hcomparison_pos.le, hgap, ?_⟩
  apply L2_recursion_geometric_bound f hf eigenvalue (Real.sqrt bound) (Real.sqrt radius)
    comparison constant (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hcomparison_pos.le
    hrate_comparison.le hconstant hbudget hzero
  intro n
  apply eLpNorm_two_le_of_integral_sq_le ((hf (n + 1)).sub ((hf n).const_smul eigenvalue))
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) n))
  have heq : (Real.sqrt bound * Real.sqrt radius ^ n) ^ 2 = bound * radius ^ n := by
    rw [mul_pow, Real.sq_sqrt hbound, ← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt hradius_pos.le]
  rw [heq]
  exact hnoise n

theorem subcritical_L2_recursion_tendsto_zero (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (eigenvalue bound radius : ℝ) (hbound : 0 ≤ bound) (hradius : 1 < radius)
    (heigenvalue : |eigenvalue| < radius)
    (hnoise : ∀ n, ∫ x, (f (n + 1) x - eigenvalue * f n x) ^ 2 ∂μ ≤ bound * radius ^ n) :
    Tendsto (fun n => eLpNorm (fun x => f n x / radius ^ n) 2 μ) atTop (𝓝 0) := by
  obtain ⟨constant, comparison, _, hcomparison, hgap, hestimate⟩ :=
    subcritical_L2_recursion_geometric_bound f hf eigenvalue bound radius hbound hradius heigenvalue hnoise
  exact L2_normalized_geometric_bound_zero f constant comparison radius hcomparison
    (lt_trans zero_lt_one hradius) hgap hestimate

theorem subcritical_L2_recursion_sum_tendsto_zero (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (eigenvalue bound radius : ℝ) (hbound : 0 ≤ bound) (hradius : 1 < radius)
    (heigenvalue : |eigenvalue| < radius)
    (hnoise : ∀ n, ∫ x, (f (n + 1) x - eigenvalue * f n x) ^ 2 ∂μ ≤ bound * radius ^ n) :
    Tendsto (fun n => eLpNorm (fun x => (∑ k ∈ Finset.range n, f k x) / radius ^ n) 2 μ) atTop (𝓝 0) := by
  obtain ⟨constant, comparison, hconstant, hcomparison, hgap, hestimate⟩ :=
    subcritical_L2_recursion_geometric_bound f hf eigenvalue bound radius hbound hradius heigenvalue hnoise
  exact geometric_L2_sum_tendsto_zero f hf constant comparison radius hconstant hcomparison hradius hgap hestimate

end
end Universality

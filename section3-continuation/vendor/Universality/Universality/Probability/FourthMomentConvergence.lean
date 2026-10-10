import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Universality
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem eLpNorm_two_le_of_integral_sq_le {f : Ω → ℝ} (hf : MemLp f 2 μ)
    {bound : ℝ} (hbound : 0 ≤ bound) (hsq : ∫ x, f x ^ 2 ∂μ ≤ bound ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal bound := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_eq_rpow]
  apply ENNReal.ofReal_le_ofReal
  exact (Real.sqrt_le_iff).mpr ⟨hbound, hsq⟩

/-- A uniform fourth-moment bound implies uniform integrability in L². -/
theorem uniformIntegrable_two_of_fourth_bound [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (hmeas : ∀ n, StronglyMeasurable (f n))
    (hsquare : ∀ n, MemLp (f n) 2 μ)
    (hfourth : ∀ n, Integrable (fun x => f n x ^ 4) μ)
    (bound : ℝ) (hbound : 0 ≤ bound) (hestimate : ∀ n, ∫ x, f n x ^ 4 ∂μ ≤ bound) :
    UniformIntegrable f 2 μ := by
  apply uniformIntegrable_of (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun n => (hmeas n).aestronglyMeasurable)
  intro ε hε
  let cutoff : ℝ≥0 := ⟨(bound + 1) / ε, (div_pos (by linarith) hε).le⟩
  have hcutoff : 0 < (cutoff : ℝ) := div_pos (by linarith) hε
  refine ⟨cutoff, fun n => ?_⟩
  have hset : MeasurableSet {x | cutoff ≤ ‖f n x‖₊} :=
    measurableSet_le measurable_const (hmeas n).measurable.nnnorm
  apply eLpNorm_two_le_of_integral_sq_le ((hsquare n).indicator hset) hε.le
  calc
    _ ≤ ∫ x, f n x ^ 4 / (cutoff : ℝ) ^ 2 ∂μ := by
      apply integral_mono ((hsquare n).indicator hset).integrable_sq ((hfourth n).div_const _)
      intro x
      change ({x | cutoff ≤ ‖f n x‖₊}.indicator (f n) x) ^ 2 ≤ f n x ^ 4 / (cutoff : ℝ) ^ 2
      by_cases hx : x ∈ {x | cutoff ≤ ‖f n x‖₊}
      · rw [Set.indicator_of_mem hx]
        apply (le_div_iff₀ (pow_pos hcutoff 2)).mpr
        have habs : (cutoff : ℝ) ≤ |f n x| := hx
        have hsq : (cutoff : ℝ) ^ 2 ≤ (f n x) ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ hcutoff.le habs 2
        nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (f n x))]
      · rw [Set.indicator_of_notMem hx]
        simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)]
        positivity
    _ ≤ bound / (cutoff : ℝ) ^ 2 := by
      rw [integral_div]
      exact div_le_div_of_nonneg_right (hestimate n) (sq_nonneg _)
    _ ≤ ε ^ 2 := by
      apply (div_le_iff₀ (pow_pos hcutoff 2)).mpr
      calc
        bound ≤ (bound + 1) ^ 2 := by nlinarith
        _ = ε ^ 2 * (cutoff : ℝ) ^ 2 := by
          change (bound + 1) ^ 2 = ε ^ 2 * ((bound + 1) / ε) ^ 2
          field_simp

theorem nonnegative_martingale_tendsto_L2 [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (filtration : Filtration ℕ ‹MeasurableSpace Ω›)
    (hmartingale : Martingale f filtration μ) (hnonneg : ∀ n x, 0 ≤ f n x)
    (hsquare : ∀ n, MemLp (f n) 2 μ)
    (hfourth : ∀ n, Integrable (fun x => f n x ^ 4) μ)
    (firstBound fourthBound : ℝ) (_hfirstBound : 0 ≤ firstBound) (hfourthBound : 0 ≤ fourthBound)
    (hfirst : ∀ n, ∫ x, f n x ∂μ ≤ firstBound)
    (hfourthEstimate : ∀ n, ∫ x, f n x ^ 4 ∂μ ≤ fourthBound) :
    ∃ limit : Ω → ℝ, MemLp limit 2 μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (limit x))) ∧
      Tendsto (fun n => eLpNorm (f n - limit) 2 μ) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : StronglyMeasurable (f n) :=
    (hmartingale.stronglyMeasurable n).mono (filtration.le n)
  have hL1 (n : ℕ) : eLpNorm (f n) 1 μ ≤ ENNReal.ofReal firstBound := by
    rw [(memLp_one_iff_integrable.mpr (hmartingale.integrable n)).eLpNorm_eq_integral_rpow_norm
      one_ne_zero ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs]
    simp_rw [abs_of_nonneg (hnonneg n _)]
    exact ENNReal.ofReal_le_ofReal (hfirst n)
  have hae := hmartingale.submartingale.ae_tendsto_limitProcess
    (R := Real.toNNReal firstBound) (by simpa only [ENNReal.ofReal] using hL1)
  have hunif := uniformIntegrable_two_of_fourth_bound f hmeas hsquare hfourth
    fourthBound hfourthBound hfourthEstimate
  have hlimit := hunif.memLp_of_ae_tendsto hae
  exact ⟨filtration.limitProcess f μ, hlimit, hae,
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      (fun n => (hmeas n).aestronglyMeasurable) hlimit hunif.unifIntegrable hae⟩

theorem martingale_L2_limit_integral [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (filtration : Filtration ℕ ‹MeasurableSpace Ω›)
    (hmartingale : Martingale f filtration μ) (limit : Ω → ℝ) (hlimit : MemLp limit 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - limit) 2 μ) atTop (𝓝 0)) :
    ∫ x, limit x ∂μ = ∫ x, f 0 x ∂μ := by
  have hL1 : Tendsto (fun n => eLpNorm (f n - limit) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le) (fun n => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
        ((hmartingale.integrable n).aestronglyMeasurable.sub hlimit.aestronglyMeasurable))
  have hintegral := tendsto_integral_of_L1' limit hlimit.aestronglyMeasurable
    (Filter.Eventually.of_forall hmartingale.integrable) hL1
  have heq (n : ℕ) : ∫ x, f n x ∂μ = ∫ x, f 0 x ∂μ := by
    have h := hmartingale.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
    simpa only [Measure.restrict_univ] using h.symm
  simp_rw [heq] at hintegral
  exact tendsto_nhds_unique hintegral tendsto_const_nhds

end
end Universality

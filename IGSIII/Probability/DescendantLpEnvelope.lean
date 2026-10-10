import IGSIII.Probability.CountableLpEnvelope
import IGSIII.Geometry.DescendantEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability
open MeasureTheory Filter
open scoped ENNReal BigOperators

lemma lintegral_enorm_natPow_eq_eLpNorm_natPow
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (function : Sample → ℝ) (power : ℕ) (positive : 0 < power) :
    (∫⁻ sample, ‖function sample‖ₑ ^ power ∂measure) = eLpNorm function power measure ^ power := by
  simpa only [NNReal.coe_natCast, ENNReal.coe_natCast, ENNReal.rpow_natCast] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := measure) (f := function) (p := (power : NNReal))
      (by exact_mod_cast positive.ne')).symm

/-- Uniform high moments, with the actual number of descendant words, give an
Lp amplitude which controls every terminal envelope at every address. -/
theorem exists_memLp_descendant_envelope
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (edges power : ℕ) (powerPositive : 0 < power)
    (functions : List (Fin edges) → Bool → Sample → ℝ)
    (measurable : ∀ address opened, Measurable (functions address opened))
    (bound : ℝ≥0∞) (boundFinite : bound ≠ ∞)
    (momentBounds : ∀ address opened, eLpNorm (functions address opened) power measure ≤ bound)
    (growth : ℝ) (growthPositive : 0 < growth)
    (decay : (edges : ℝ≥0∞) * (ENNReal.ofReal growth)⁻¹ ^ power < 1) :
    ∃ envelope : Sample → ℝ, Measurable envelope ∧ MemLp envelope power measure ∧
      (∀ sample, 0 ≤ envelope sample) ∧ ∀ᵐ sample ∂measure, ∀ address opened,
        ‖functions address opened sample‖ ≤ envelope sample * growth ^ address.length := by
  let normalized : (Σ depth : ℕ, (Fin depth → Fin edges) × Bool) → Sample → ℝ :=
    fun index sample => (growth⁻¹ ^ index.1) * functions (List.ofFn index.2.1) index.2.2 sample
  have normalizedMeasurable (index : Σ depth : ℕ, (Fin depth → Fin edges) × Bool) :
      Measurable (normalized index) := (measurable _ _).const_mul _
  have singleBound (depth : ℕ) (word : Fin depth → Fin edges) (opened : Bool) :
      (∫⁻ sample, ‖normalized ⟨depth, word, opened⟩ sample‖ₑ ^ power ∂measure) ≤
        (ENNReal.ofReal growth)⁻¹ ^ (depth * power) * bound ^ power := by
    rw [lintegral_enorm_natPow_eq_eLpNorm_natPow measure _ power powerPositive]
    have normBound : eLpNorm (normalized ⟨depth, word, opened⟩) power measure ≤
        (ENNReal.ofReal growth)⁻¹ ^ depth * bound := by
      change eLpNorm ((growth⁻¹ ^ depth) • functions (List.ofFn word) opened) power measure ≤ _
      rw [eLpNorm_const_smul]
      rw [Real.enorm_of_nonneg (pow_nonneg (inv_nonneg.mpr growthPositive.le) depth),
        ENNReal.ofReal_pow (inv_nonneg.mpr growthPositive.le), ENNReal.ofReal_inv_of_pos growthPositive]
      exact mul_le_mul_left' (momentBounds _ _) _
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left' normBound power
  have levelBound (depth : ℕ) :
      (∑' pair : (Fin depth → Fin edges) × Bool,
        ∫⁻ sample, ‖normalized ⟨depth, pair⟩ sample‖ₑ ^ power ∂measure) ≤
      (2 * bound ^ power) * ((edges : ℝ≥0∞) * (ENNReal.ofReal growth)⁻¹ ^ power) ^ depth := by
    rw [ENNReal.tsum_prod']
    simp only [tsum_fintype]
    calc
      _ ≤ ∑ _word : Fin depth → Fin edges, ∑ _opened : Bool,
          (ENNReal.ofReal growth)⁻¹ ^ (depth * power) * bound ^ power :=
        Finset.sum_le_sum (fun word _ => Finset.sum_le_sum (fun opened _ => singleBound depth word opened))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        rw [mul_pow, ← pow_mul, Nat.mul_comm power depth]
        ring
  have sumFinite : (∑' index, ∫⁻ sample, ‖normalized index sample‖ₑ ^ power ∂measure) ≠ ∞ := by
    rw [ENNReal.tsum_sigma']
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum levelBound)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top boundFinite))
      (tsum_geometric_lt_top.mpr decay).ne
  obtain ⟨envelope, envelopeMeasurable, envelopeMemLp, envelopeNonnegative, envelopeBounds⟩ :=
    exists_memLp_countable_envelope measure power powerPositive normalized normalizedMeasurable sumFinite
  refine ⟨envelope, envelopeMeasurable, envelopeMemLp, envelopeNonnegative, ?_⟩
  filter_upwards [envelopeBounds] with sample bounds
  intro address opened
  have normalizedBound := bounds ⟨address.length, address.get, opened⟩
  change ‖growth⁻¹ ^ address.length * functions (List.ofFn address.get) opened sample‖ ≤ envelope sample at normalizedBound
  rw [List.ofFn_get, norm_mul, Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr growthPositive.le) _)] at normalizedBound
  have boundAfterMultiplication := mul_le_mul_of_nonneg_right normalizedBound (pow_pos growthPositive address.length).le
  calc
    ‖functions address opened sample‖ =
        (growth⁻¹ ^ address.length * ‖functions address opened sample‖) * growth ^ address.length := by
          rw [inv_pow]
          field_simp [growthPositive.ne']
    _ ≤ envelope sample * growth ^ address.length := boundAfterMultiplication

end IGSIII.Probability


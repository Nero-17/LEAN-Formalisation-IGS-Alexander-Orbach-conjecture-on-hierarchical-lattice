import Universality.Probability.InitialMomentComparison

namespace Universality
noncomputable section

/-- A positive lower bound on reference moments converts a uniform
finite-order moment bound into a graded comparison. -/
theorem graded_moment_comparison_of_bounds {ι : Type*}
    (first reference : ι → ℕ → ℝ) (order : ℕ) (constant growth lower : ℝ)
    (hconstant : 0 ≤ constant) (hgrowth : 1 ≤ growth) (hlower : 0 < lower)
    (hfirstZero : ∀ state, first state 0 = 1) (hreferenceZero : ∀ state, reference state 0 = 1)
    (hfirst : ∀ state k, k ≤ order → first state k ≤ constant * growth ^ k)
    (hreference : ∀ state k, k ≤ order → lower ≤ reference state k) :
    ∀ state k, k ≤ order → first state k ≤
      (max 1 (constant / lower) * growth) ^ k * reference state k := by
  intro state k hk
  by_cases hzero : k = 0
  · simp [hzero, hfirstZero, hreferenceZero]
  have hscale : 1 ≤ max 1 (constant / lower) := le_max_left _ _
  have hscaleNonneg : 0 ≤ max 1 (constant / lower) := zero_le_one.trans hscale
  have hconstantBound : constant ≤ max 1 (constant / lower) * lower :=
    (div_le_iff₀ hlower).mp (le_max_right _ _)
  have hpower : max 1 (constant / lower) ≤ max 1 (constant / lower) ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ hscale (show 1 ≤ k by omega)
  have hcoefficient : constant ≤ max 1 (constant / lower) ^ k * reference state k :=
    hconstantBound.trans (mul_le_mul hpower (hreference state k hk) hlower.le (pow_nonneg hscaleNonneg _))
  calc
    _ ≤ constant * growth ^ k := hfirst state k hk
    _ ≤ (max 1 (constant / lower) ^ k * reference state k) * growth ^ k :=
      mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg (zero_le_one.trans hgrowth) _)
    _ = _ := by rw [mul_pow]; ring

end
end Universality

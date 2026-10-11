import Universality.Analysis.StoppedGeometricLogBound

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem tendsto_ratio_of_bounded_error_atTop {α : Type*} (filter : Filter α)
    (first second : α → ℝ) (coefficient bound : ℝ) (hsecond : Tendsto second filter atTop)
    (herror : ∀ᶠ x in filter, |first x - coefficient * second x| ≤ bound) :
    Tendsto (fun x => first x / second x) filter (𝓝 coefficient) := by
  have hh := tendsto_ratio_of_bounded_error filter first (fun x => -second x) (-coefficient) bound
    (tendsto_neg_atTop_atBot.comp hsecond) (by simpa only [neg_mul_neg] using herror)
  simpa only [div_neg, neg_neg] using hh.neg

/-- A nearest-power spatial scale introduces a bounded logarithmic error.
The factor `size` is the exact conversion from cluster density to root law. -/
theorem size_scaled_geometric_log_error (response size growth scale lower upper : ℝ)
    (depth : ℕ) (hsize : 0 < size) (hgrowth : 1 < growth) (hscale : 0 < scale)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsizeLower : growth ^ depth ≤ size) (hsizeUpper : size ≤ growth ^ (depth + 1))
    (hresponseLower : lower * (size * scale ^ depth) ≤ response)
    (hresponseUpper : response ≤ upper * (size * scale ^ depth)) :
    |Real.log response - (1 + Real.log scale / Real.log growth) * Real.log size| ≤
      |Real.log lower| + |Real.log upper| + |Real.log scale / Real.log growth| * Real.log growth := by
  have hr : 0 < growth := zero_lt_one.trans hgrowth
  have hlog : 0 < Real.log growth := Real.log_pos hgrowth
  have hresponse : 0 < response := (mul_pos hlower (mul_pos hsize (pow_pos hscale _))).trans_le hresponseLower
  have hl : lower * scale ^ depth ≤ response / size :=
    (le_div_iff₀ hsize).mpr (by nlinarith only [hresponseLower])
  have hu : response / size ≤ upper * scale ^ depth :=
    (div_le_iff₀ hsize).mpr (by nlinarith only [hresponseUpper])
  have hmass := log_error_of_geometric_comparison (response / size) scale lower upper depth hscale hlower hupper hl hu
  rw [Real.log_div hresponse.ne' hsize.ne'] at hmass
  have hleft := Real.log_le_log (pow_pos hr depth) hsizeLower
  have hright := Real.log_le_log hsize hsizeUpper
  rw [Real.log_pow] at hleft hright
  simp only [Nat.cast_add, Nat.cast_one] at hright
  have hscaleError : |(depth : ℝ) * Real.log growth - Real.log size| ≤ Real.log growth :=
    abs_le.mpr ⟨by nlinarith only [hright], by linarith⟩
  have heq : Real.log response - (1 + Real.log scale / Real.log growth) * Real.log size =
      (Real.log response - Real.log size - (depth : ℝ) * Real.log scale) +
        (Real.log scale / Real.log growth) * ((depth : ℝ) * Real.log growth - Real.log size) := by
    field_simp [hlog.ne']
    <;> ring
  rw [heq]
  calc
    _ ≤ |Real.log response - Real.log size - (depth : ℝ) * Real.log scale| +
        |(Real.log scale / Real.log growth) * ((depth : ℝ) * Real.log growth - Real.log size)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add hmass (mul_le_mul_of_nonneg_left hscaleError (abs_nonneg _))

end
end Universality

import IGSIII4.SpectralDensity.ActualMomentFinitePath

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {Path : Type*} [Fintype Path]

def successfulPathCount (success : Path → Bool) : ℝ :=
  ∑ path, if success path = true then 1 else 0

def parallelBlockResponse (success : Path → Bool) (pathResistance : Path → ℝ) : ℝ :=
  (∑ path, if success path = true then (pathResistance path)⁻¹ else 0)⁻¹

theorem successfulPathCount_positive (success : Path → Bool)
    (crosses : ∃ path, success path = true) : 0 < successfulPathCount success := by
  obtain ⟨path, opened⟩ := crosses
  apply Finset.sum_pos' (fun other _ => by split_ifs <;> norm_num)
  exact ⟨path, Finset.mem_univ _, by simp only [opened, ↓reduceIte]; norm_num⟩

theorem parallelBlockResponse_nonnegative (success : Path → Bool)
    (pathResistance : Path → ℝ) (positive : ∀ path, 0 < pathResistance path) :
    0 ≤ parallelBlockResponse success pathResistance := by
  apply inv_nonneg.mpr
  apply Finset.sum_nonneg
  intro path _
  split_ifs
  · exact (inv_pos.mpr (positive path)).le
  · exact le_rfl

theorem parallelBlockResponse_le_path (success : Path → Bool)
    (pathResistance : Path → ℝ) (positive : ∀ path, 0 < pathResistance path)
    (path : Path) (opened : success path = true) :
    parallelBlockResponse success pathResistance ≤ pathResistance path := by
  have comparison : (pathResistance path)⁻¹ ≤
      ∑ other, if success other = true then (pathResistance other)⁻¹ else 0 := by
    have nonnegative : ∀ other ∈ (Finset.univ : Finset Path),
        0 ≤ (if success other = true then (pathResistance other)⁻¹ else 0) := by
      intro other _
      split_ifs
      · exact (inv_pos.mpr (positive other)).le
      · exact le_rfl
    simpa only [opened, ↓reduceIte] using Finset.single_le_sum nonnegative (Finset.mem_univ path)
  have inverse := one_div_le_one_div_of_le (inv_pos.mpr (positive path)) comparison
  simpa only [one_div, inv_inv, parallelBlockResponse] using inverse

theorem parallelBlockResponse_lower (success : Path → Bool)
    (pathResistance : Path → ℝ) (positive : ∀ path, 0 < pathResistance path)
    (crosses : ∃ path, success path = true) (threshold : ℝ) (thresholdNonnegative : 0 ≤ threshold)
    (good : ∀ path, success path = true → threshold ≤ pathResistance path) :
    threshold / successfulPathCount success ≤ parallelBlockResponse success pathResistance := by
  obtain ⟨selected, selectedOpen⟩ := crosses
  have countPositive := successfulPathCount_positive success ⟨selected, selectedOpen⟩
  have conductancePositive : 0 < ∑ path, if success path = true then (pathResistance path)⁻¹ else 0 := by
    apply Finset.sum_pos' (fun path _ => by split_ifs; exact (inv_pos.mpr (positive path)).le; exact le_rfl)
    exact ⟨selected, Finset.mem_univ _, by simpa only [selectedOpen, ↓reduceIte] using inv_pos.mpr (positive selected)⟩
  have comparison : threshold * (∑ path, if success path = true then (pathResistance path)⁻¹ else 0) ≤
      successfulPathCount success := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro path _
    by_cases opened : success path = true
    · simp only [opened, ↓reduceIte]
      rw [← div_eq_mul_inv]
      exact (div_le_one (positive path)).mpr (good path opened)
    · simp [opened]
  rw [parallelBlockResponse, ← one_div]
  apply (le_div_iff₀ conductancePositive).mpr
  rw [div_mul_eq_mul_div, div_le_iff₀ countPositive, one_mul]
  exact comparison

theorem parallelBlockResponse_lower_with_bad_count (success : Path → Bool)
    (pathResistance : Path → ℝ) (positive : ∀ path, 0 < pathResistance path)
    (crosses : ∃ path, success path = true) (threshold : ℝ) (thresholdNonnegative : 0 ≤ threshold) :
    threshold / successfulPathCount success *
      (1 - ∑ path, if success path = true ∧ pathResistance path < threshold then (1 : ℝ) else 0) ≤
        parallelBlockResponse success pathResistance := by
  classical
  by_cases bad : ∃ path, success path = true ∧ pathResistance path < threshold
  · obtain ⟨path, opened, below⟩ := bad
    have badCount : (1 : ℝ) ≤ ∑ other, if success other = true ∧ pathResistance other < threshold then (1 : ℝ) else 0 := by
      have nonnegative : ∀ other ∈ (Finset.univ : Finset Path),
          0 ≤ (if success other = true ∧ pathResistance other < threshold then (1 : ℝ) else 0) := by
        intro other _
        split_ifs <;> norm_num
      simpa only [opened, below, and_self, ↓reduceIte] using
        Finset.single_le_sum nonnegative (Finset.mem_univ path)
    have sign : 0 ≤ threshold / successfulPathCount success :=
      div_nonneg thresholdNonnegative (successfulPathCount_positive success crosses).le
    exact (mul_nonpos_of_nonneg_of_nonpos sign (sub_nonpos.mpr badCount)).trans
      (parallelBlockResponse_nonnegative success pathResistance positive)
  · have good : ∀ path, success path = true → threshold ≤ pathResistance path := by
      intro path opened
      exact le_of_not_gt (fun below => bad ⟨path, opened, below⟩)
    have zeroBad (path : Path) :
        (if success path = true ∧ pathResistance path < threshold then (1 : ℝ) else 0) = 0 := by
      split_ifs with badPath
      · exact False.elim (bad ⟨path, badPath⟩)
      · rfl
    simpa only [zeroBad, Finset.sum_const_zero, sub_zero, mul_one] using
      parallelBlockResponse_lower success pathResistance positive crosses threshold thresholdNonnegative good

end
end IGSIII4.SpectralDensity

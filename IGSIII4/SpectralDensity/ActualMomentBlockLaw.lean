import IGSIII4.SpectralDensity.ActualMomentParallelBlock

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
open IGSIII34.Probability
attribute [local instance] Classical.propDecidable
variable {Path Outcome : Type*} [Fintype Path] [DecidableEq Path]
  [Fintype Outcome] [Nonempty Outcome] {length : ℕ}

def pathInputResistance (response : Outcome → ℝ) (input : Fin length → Outcome) : ℝ :=
  ∑ edge, response (input edge)

def blockProductWeight (weight : Outcome → ℝ) (input : Path → Fin length → Outcome) : ℝ :=
  productWeight (productWeight weight) input

def blockInputResponse (success : Path → Bool) (response : Outcome → ℝ)
    (input : Path → Fin length → Outcome) : ℝ :=
  parallelBlockResponse success (fun path => pathInputResistance response (input path))

theorem pathInputResistance_positive (response : Outcome → ℝ)
    (positive : ∀ outcome, 0 < response outcome) (lengthPositive : 0 < length)
    (input : Fin length → Outcome) : 0 < pathInputResistance response input := by
  haveI : NeZero length := ⟨Nat.ne_of_gt lengthPositive⟩
  exact Finset.sum_pos (fun edge _ => positive (input edge)) Finset.univ_nonempty

theorem blockProductWeight_normalized (weight : Outcome → ℝ)
    (normalized : ∑ outcome, weight outcome = 1) :
    (∑ input : Path → Fin length → Outcome, blockProductWeight weight input) = 1 :=
  sum_productWeight _ (sum_productWeight weight normalized)

theorem finiteMean_sum {Index Sample : Type*} [Fintype Index] [Fintype Sample]
    (weight : Sample → ℝ) (response : Index → Sample → ℝ) :
    finiteMean weight (fun sample => ∑ index, response index sample) =
      ∑ index, finiteMean weight (response index) := by
  simp only [finiteMean, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Fixed successful-path statuses: the second moment is bounded by that of
the first selected successful independent path. No status/resistance dependence is assumed. -/
theorem finiteMean_block_second_moment (success : Path → Bool)
    (crosses : ∃ path, success path = true) (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (positive : ∀ outcome, 0 < response outcome) (lengthPositive : 0 < length)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    finiteMean (blockProductWeight weight)
      (fun input : Path → Fin length → Outcome => blockInputResponse success response input ^ 2) ≤
        (length : ℝ) ^ 2 + 8 * length := by
  obtain ⟨selected, opened⟩ := crosses
  have pathWeightNonnegative : ∀ input : Fin length → Outcome, 0 ≤ productWeight weight input :=
    productWeight_nonnegative weight weightNonnegative
  have pointwise (input : Path → Fin length → Outcome) :
      blockInputResponse success response input ^ 2 ≤ pathInputResistance response (input selected) ^ 2 := by
    have resistancePositive := pathInputResistance_positive response positive lengthPositive
    have lower := parallelBlockResponse_nonnegative success
      (fun path => pathInputResistance response (input path)) (fun path => resistancePositive (input path))
    have upper := parallelBlockResponse_le_path success
      (fun path => pathInputResistance response (input path)) (fun path => resistancePositive (input path)) selected opened
    exact pow_le_pow_left₀ lower upper 2
  have comparison : finiteMean (blockProductWeight weight)
      (fun input : Path → Fin length → Outcome => blockInputResponse success response input ^ 2) ≤
        finiteMean (blockProductWeight weight)
          (fun input : Path → Fin length → Outcome => pathInputResistance response (input selected) ^ 2) := by
    exact Finset.sum_le_sum (fun input _ => mul_le_mul_of_nonneg_left (pointwise input)
      (productWeight_nonnegative _ pathWeightNonnegative input))
  have marginal := finiteMean_coordinate (productWeight (Edge := Fin length) weight)
    (sum_productWeight weight normalized) selected (fun input => pathInputResistance response input ^ 2)
  change finiteMean (blockProductWeight weight)
    (fun input : Path → Fin length → Outcome => pathInputResistance response (input selected) ^ 2) = _ at marginal
  rw [marginal] at comparison
  exact comparison.trans (by simpa only [pathInputResistance, Fintype.card_fin] using
    finiteMean_path_second_moment (Coordinate := Fin length) weight response normalized meanOne varianceBound)

theorem finiteMean_block_lower (success : Path → Bool)
    (crosses : ∃ path, success path = true) (weight response : Outcome → ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (positive : ∀ outcome, 0 < response outcome) (lengthPositive : 0 < length)
    (meanOne : finiteMean weight response = 1) (varianceBound : finiteVariance weight response ≤ 8) :
    (length : ℝ) / 2 / successfulPathCount success - (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length ≤
      finiteMean (blockProductWeight weight)
        (fun input : Path → Fin length → Outcome => blockInputResponse success response input) := by
  let badCount (input : Path → Fin length → Outcome) : ℝ :=
    ∑ path, if success path = true ∧ pathInputResistance response (input path) < (length : ℝ) / 2 then 1 else 0
  have countPositive := successfulPathCount_positive success crosses
  have pathWeightNonnegative : ∀ input : Fin length → Outcome, 0 ≤ productWeight weight input :=
    productWeight_nonnegative weight weightNonnegative
  have badMean : finiteMean (blockProductWeight weight) badCount ≤
      successfulPathCount success * (69 / 70 : ℝ) ^ length := by
    rw [show badCount = (fun input : Path → Fin length → Outcome => ∑ path,
      if success path = true ∧ pathInputResistance response (input path) < (length : ℝ) / 2 then 1 else 0) from rfl,
      finiteMean_sum]
    unfold successfulPathCount
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro path _
    by_cases opened : success path = true
    · simp only [opened, true_and, ↓reduceIte, one_mul]
      rw [show blockProductWeight weight = productWeight (Edge := Path)
          (productWeight (Edge := Fin length) weight) from rfl,
        finiteMean_coordinate _ (sum_productWeight weight normalized) path
          (fun input : Fin length → Outcome => if pathInputResistance response input < (length : ℝ) / 2 then (1 : ℝ) else 0)]
      simpa only [pathInputResistance, Fintype.card_fin] using
        finiteMean_path_lower_tail (Coordinate := Fin length) weight response weightNonnegative
          normalized (fun outcome => (positive outcome).le) meanOne varianceBound
    · simp only [opened, false_and, ↓reduceIte, mul_zero, zero_mul, finiteMean]
      simp
  have pointwise (input : Path → Fin length → Outcome) :
      (length : ℝ) / 2 / successfulPathCount success * (1 - badCount input) ≤
        blockInputResponse success response input :=
    parallelBlockResponse_lower_with_bad_count success _
      (fun path => pathInputResistance_positive response positive lengthPositive (input path))
      crosses _ (by positivity)
  have comparison : finiteMean (blockProductWeight weight)
      (fun input : Path → Fin length → Outcome => (length : ℝ) / 2 / successfulPathCount success * (1 - badCount input)) ≤
        finiteMean (blockProductWeight weight) (fun input => blockInputResponse success response input) :=
    Finset.sum_le_sum (fun input _ => mul_le_mul_of_nonneg_left (pointwise input)
      (productWeight_nonnegative _ pathWeightNonnegative input))
  have average : finiteMean (blockProductWeight weight)
      (fun input : Path → Fin length → Outcome => (length : ℝ) / 2 / successfulPathCount success * (1 - badCount input)) =
        (length : ℝ) / 2 / successfulPathCount success *
          (1 - finiteMean (blockProductWeight weight) badCount) := by
    simp only [finiteMean, mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, blockProductWeight_normalized weight normalized, one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro input _
    ring
  rw [average] at comparison
  have coefficientNonnegative : 0 ≤ (length : ℝ) / 2 / successfulPathCount success := by positivity
  have multiplied := mul_le_mul_of_nonneg_left badMean coefficientNonnegative
  have cancellation : (length : ℝ) / 2 / successfulPathCount success *
      (successfulPathCount success * (69 / 70 : ℝ) ^ length) =
        (length : ℝ) / 2 * (69 / 70 : ℝ) ^ length := by
    field_simp [ne_of_gt countPositive]
  rw [cancellation] at multiplied
  linarith

end
end IGSIII4.SpectralDensity

import IGSIII4.SpectralDensity.ActualPathMassActive
import IGSIII4.SpectralDensity.ActualPathMassProbability
import IGSIII4.SpectralDensity.ActualMassGrowth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork Matrix Filter Topology
open scoped BigOperators

theorem expectation_finite_sum {edges : ℕ} {Index : Type*} [Fintype Index]
    (probability : ℝ) (response : Index → Configuration edges → ℝ) :
    expectation probability (fun configuration => ∑ index, response index configuration) =
      ∑ index, expectation probability (response index) := by
  unfold expectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem path_event_count_nonnegative (blocks paths interior : ℕ)
    (configuration : Edge blocks paths interior → Bool) :
    0 ≤ ∑ block : Fin blocks, ∑ path : Fin paths, ∑ edge : Fin (interior + 2),
      if EdgeEndEvent blocks paths interior configuration block path edge then (1 : ℝ) else 0 := by
  apply Finset.sum_nonneg
  intro block _
  apply Finset.sum_nonneg
  intro path _
  apply Finset.sum_nonneg
  intro edge _
  split_ifs <;> norm_num

theorem actual_mass_row_path_upper (blocks paths interior : ℕ) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1) (state : LiveState)
    (conditioningPositive : 0 < (network blocks paths interior).conditioningProbability probability state) :
    (∑ child, (network blocks paths interior).massMatrix probability state child) ≤
      4 + ((blocks * paths : ℕ) : ℝ) * (2 / (1 - probability)) /
        (network blocks paths interior).conditioningProbability probability state := by
  have response : (∑ child, (network blocks paths interior).massMatrix probability state child) =
      (network blocks paths interior).conditionalResponse probability state (fun _ => 1) := by
    simpa only [Matrix.mulVec, dotProduct, mul_one] using
      (network blocks paths interior).massMatrix_mulVec_response probability (fun _ => 1) state
  rw [response, conditionalResponse]
  have pointwise (configuration : Configuration (Fintype.card (Edge blocks paths interior))) :
      (if (network blocks paths interior).conditioning state configuration then
        bernoulliWeight probability configuration * (network blocks paths interior).liveResponse state configuration (fun _ => 1) else 0) ≤
      4 * (if (network blocks paths interior).conditioning state configuration then bernoulliWeight probability configuration else 0) +
        bernoulliWeight probability configuration *
          (∑ block : Fin blocks, ∑ path : Fin paths, ∑ edge : Fin (interior + 2),
            if EdgeEndEvent blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge)) block path edge then (1 : ℝ) else 0) := by
    have bound := liveResponse_path_end_upper blocks paths interior state (fun edge => configuration (Fintype.equivFin _ edge))
    simp only [Equiv.apply_symm_apply] at bound
    have nonnegative := path_event_count_nonnegative blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge))
    split_ifs
    · nlinarith [mul_le_mul_of_nonneg_left bound (bernoulliWeight_nonneg positive.le belowOne.le configuration)]
    · simpa only [mul_zero, zero_add] using
        mul_nonneg (bernoulliWeight_nonneg positive.le belowOne.le configuration) nonnegative
  have numeratorBound := Finset.sum_le_sum (fun configuration (_ : configuration ∈ Finset.univ) => pointwise configuration)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at numeratorBound
  change _ ≤ 4 * (network blocks paths interior).conditioningProbability probability state +
      expectation probability (fun configuration =>
        ∑ block : Fin blocks, ∑ path : Fin paths, ∑ edge : Fin (interior + 2),
          if EdgeEndEvent blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge)) block path edge then (1 : ℝ) else 0) at numeratorBound
  simp_rw [expectation_finite_sum] at numeratorBound
  have pathSumsBound : (∑ block : Fin blocks, ∑ path : Fin paths, ∑ edge : Fin (interior + 2),
      expectation probability (fun configuration : Configuration (Fintype.card (Edge blocks paths interior)) =>
        if EdgeEndEvent blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge)) block path edge then (1 : ℝ) else 0)) ≤
        ((blocks * paths : ℕ) : ℝ) * (2 / (1 - probability)) := by
    calc
      _ ≤ ∑ _ : Fin blocks, ∑ _ : Fin paths, 2 / (1 - probability) := by
        apply Finset.sum_le_sum
        intro block _
        apply Finset.sum_le_sum
        intro path _
        exact (path_end_probability_sum_lt blocks paths interior block path probability positive belowOne).le
      _ = _ := by simp [Nat.cast_mul]; ring
  apply (div_le_iff₀ conditioningPositive).mpr
  have finalBound := numeratorBound.trans (add_le_add le_rfl pathSumsBound)
  have cancellation :
      (4 + ((blocks * paths : ℕ) : ℝ) * (2 / (1 - probability)) /
        (network blocks paths interior).conditioningProbability probability state) *
        (network blocks paths interior).conditioningProbability probability state =
      4 * (network blocks paths interior).conditioningProbability probability state +
        ((blocks * paths : ℕ) : ℝ) * (2 / (1 - probability)) := by field_simp [conditioningPositive.ne']
  rw [cancellation]
  exact finalBound

theorem actual_mass_row_sharp_upper (blocks paths interior : ℕ) (countsPositive : 0 < blocks * paths)
    (probability : ℝ) (above : 7 / 10 < probability) (below : probability < 4 / 5)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) (state : LiveState) :
    (∑ child, (network blocks paths interior).massMatrix probability state child) <
      4 + 50 * ((blocks * paths : ℕ) : ℝ) := by
  have positive : 0 < probability := by linarith
  have belowOne : probability < 1 := by linarith
  have conditioningLower : 1 / 5 < (network blocks paths interior).conditioningProbability probability state := by
    cases state
    · rw [conditioningProbability_connected, fixedPoint]; linarith
    · rw [conditioningProbability_both, fixedPoint]; linarith
    · rw [conditioningProbability_single, fixedPoint]; linarith
  have pathBound := actual_mass_row_path_upper blocks paths interior probability positive belowOne state (by linarith)
  have coefficientBound : (2 / (1 - probability)) /
      (network blocks paths interior).conditioningProbability probability state < 50 := by
    rw [div_div]
    apply (div_lt_iff₀ (by positivity : 0 < (1 - probability) *
      (network blocks paths interior).conditioningProbability probability state)).mpr
    have productLower : (1 / 25 : ℝ) < (1 - probability) *
        (network blocks paths interior).conditioningProbability probability state := by
      calc
        _ = (1 / 5 : ℝ) * (1 / 5) := by norm_num
        _ < (1 - probability) * (1 / 5) := mul_lt_mul_of_pos_right (by linarith) (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_left conditioningLower.le (by linarith)
    nlinarith [productLower]
  have countsRealPositive : 0 < ((blocks * paths : ℕ) : ℝ) := by exact_mod_cast countsPositive
  have strictBound := mul_lt_mul_of_pos_left coefficientBound countsRealPositive
  have rearrange : ((blocks * paths : ℕ) : ℝ) * ((2 / (1 - probability)) /
      (network blocks paths interior).conditioningProbability probability state) =
      ((blocks * paths : ℕ) : ℝ) * (2 / (1 - probability)) /
        (network blocks paths interior).conditioningProbability probability state := by ring
  rw [rearrange] at strictBound
  nlinarith

theorem positive_eigenvalue_lt_row_upper {State : Type*} [Fintype State] [Nonempty State]
    (matrix : Matrix State State ℝ) (vector : State → ℝ) (radius bound : ℝ)
    (nonnegative : ∀ first second, 0 ≤ matrix first second)
    (positiveVector : ∀ state, 0 < vector state) (eigenvector : matrix *ᵥ vector = radius • vector)
    (rowBounds : ∀ first, ∑ second, matrix first second < bound) : radius < bound := by
  obtain ⟨maximum, _, maximal⟩ := Finset.exists_max_image Finset.univ vector Finset.univ_nonempty
  have equation := congrFun eigenvector maximum
  change (∑ second, matrix maximum second * vector second) = radius * vector maximum at equation
  apply (mul_lt_mul_iff_of_pos_right (positiveVector maximum)).mp
  calc
    _ = ∑ second, matrix maximum second * vector second := equation.symm
    _ ≤ ∑ second, matrix maximum second * vector maximum := Finset.sum_le_sum
      (fun second _ => mul_le_mul_of_nonneg_left (maximal second (Finset.mem_univ _)) (nonnegative maximum second))
    _ = (∑ second, matrix maximum second) * vector maximum := (Finset.sum_mul ..).symm
    _ < _ := mul_lt_mul_of_pos_right (rowBounds maximum) (positiveVector maximum)

theorem appendix_actual_mass_sharp_upper (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length) <
        50 * (blockCount base length : ℝ) * (pathCount length : ℝ) + 4 := by
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    eventually_ge_atTop (2 : ℕ)] with length interval lengthLarge
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthLarge
  have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
  have pathsPositive : 0 < pathCount length := Nat.ceil_pos.mpr (by positivity : 0 < (length : ℝ) * (4 / 3 : ℝ) ^ length)
  obtain ⟨_, vector, positiveVector, eigenvector⟩ :=
    (appendixRule_classical base length lengthLarge).mass_spectralRadius_positive_eigenvector _ positive belowOne
  have bound := positive_eigenvalue_lt_row_upper ((appendixRule base length).network.massMatrix (appendixCriticalProbability base length))
    vector (actualMassGrowth (appendixRule base length) (appendixCriticalProbability base length))
    (4 + 50 * ((blockCount base length * pathCount length : ℕ) : ℝ))
    ((appendixRule base length).network.massMatrix_nonneg positive.le belowOne.le) positiveVector eigenvector
    (actual_mass_row_sharp_upper (blockCount base length) (pathCount length) (length - 2)
      (Nat.mul_pos blocksPositive pathsPositive) _ interval.1 interval.2 fixedPoint)
  simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm, add_comm] using bound

end
end IGSIII4.SpectralDensity.ActualFamily

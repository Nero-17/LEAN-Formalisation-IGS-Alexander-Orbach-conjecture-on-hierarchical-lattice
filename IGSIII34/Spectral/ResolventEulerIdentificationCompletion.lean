import IGSIII34.Spectral.EulerSemigroupCompletion
import IGSIII34.Spectral.ParameterFormSpectrumCompletion
import Mathlib.MeasureTheory.Function.LpOrder

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace IGSIII34.Diffusion Filter
open scoped Topology NNReal

variable {Energy L2 Index : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

theorem normalized_resolvent_euler_scalar_completion
    (eigenvalue time : ℝ) (eigenvaluePositive : 0 < eigenvalue)
    (generatorNonnegative : 0 ≤ eigenvalue⁻¹-1) (timePositive : 0 < time)
    (steps : ℕ) (stepsPositive : 0 < steps) (timeBelowSteps : time ≤ (steps : ℝ)) :
    ((steps : ℝ)/time) * (eigenvalue/(1+((steps : ℝ)/time-1)*eigenvalue)) =
      (1+time*(eigenvalue⁻¹-1)/(steps : ℝ))⁻¹ := by
  have stepsPositiveReal : 0 < (steps : ℝ) := Nat.cast_pos.mpr stepsPositive
  have parameterAboveOne : 1 ≤ (steps : ℝ)/time := (one_le_div timePositive).mpr timeBelowSteps
  have leftDenominatorPositive : 0 < 1+((steps : ℝ)/time-1)*eigenvalue := by
    nlinarith [mul_nonneg (sub_nonneg.mpr parameterAboveOne) eigenvaluePositive.le]
  have rightDenominatorPositive : 0 < 1+time*(eigenvalue⁻¹-1)/(steps : ℝ) := by
    nlinarith [div_nonneg (mul_nonneg timePositive.le generatorNonnegative) stepsPositiveReal.le]
  field_simp [eigenvaluePositive.ne', timePositive.ne', stepsPositiveReal.ne',
    leftDenominatorPositive.ne', rightDenominatorPositive.ne']
  <;> ring

theorem continuousLinearMap_eq_on_hilbert_basis_completion
    (basis : HilbertBasis Index ℝ L2) (first second : L2 →L[ℝ] L2)
    (equal : ∀ index, first (basis index) = second (basis index)) : first = second := by
  ext value
  have firstSum := (basis.hasSum_repr value).mapL first
  have secondSum := (basis.hasSum_repr value).mapL second
  have equalSummands : (fun index => first (basis.repr value index • basis index)) =
      (fun index => second (basis.repr value index • basis index)) := by
    funext index
    rw [map_smul, map_smul, equal]
  rw [equalSummands] at firstSum
  exact firstSum.unique secondSum

theorem continuousLinearMap_power_eigenvector_completion
    (operator : L2 →L[ℝ] L2) (vector : L2) (eigenvalue : ℝ)
    (eigenvector : operator vector = eigenvalue • vector) (steps : ℕ) :
    (operator ^ steps) vector = eigenvalue ^ steps • vector := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, eigenvector, map_smul, inductionHypothesis,
      smul_smul, pow_succ']

theorem parameter_resolvent_power_eq_euler_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (basis : HilbertBasis Index ℝ L2) (eigenvalues : Index → ℝ)
    (eigenvaluesPositive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, anchoredL2ResolventCompletion embedding anchorEvaluation baseCoercive
      (basis index) = eigenvalues index • basis index)
    (generatorNonnegative : ∀ index, 0 ≤ (eigenvalues index)⁻¹-1)
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) (steps : ℕ)
    (stepsPositive : 0 < steps) (timeBelowSteps : (time : ℝ) ≤ (steps : ℝ)) :
    (((steps : ℝ)/(time : ℝ)) • embedding.comp
      (parameterEnergySolutionCompletion embedding anchorEvaluation baseCoercive
        ((steps : ℝ)/(time : ℝ)) ((one_le_div timePositive).mpr timeBelowSteps))) ^ steps =
    eulerSpectralSemigroupCompletion basis (fun index => (eigenvalues index)⁻¹-1)
      generatorNonnegative time steps := by
  apply continuousLinearMap_eq_on_hilbert_basis_completion basis
  intro index
  have eigenvector :
      (((steps : ℝ)/(time : ℝ)) • embedding.comp
        (parameterEnergySolutionCompletion embedding anchorEvaluation baseCoercive
          ((steps : ℝ)/(time : ℝ)) ((one_le_div timePositive).mpr timeBelowSteps))) (basis index) =
      (1+(time : ℝ)*((eigenvalues index)⁻¹-1)/(steps : ℝ))⁻¹ • basis index := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      parameterL2Solution_eigenvalue_completion _ _ _ _ _ _ _ (eigenvaluesPositive index) (eigenvectors index),
      smul_smul, normalized_resolvent_euler_scalar_completion _ _ (eigenvaluesPositive index)
        (generatorNonnegative index) timePositive steps stepsPositive timeBelowSteps]
  rw [continuousLinearMap_power_eigenvector_completion _ _ _ eigenvector,
    eulerSpectralSemigroupCompletion, hilbertBoundedDiagonal_basis_completion]
  rfl

theorem continuousLinearMap_power_fixed_completion
    (operator : L2 →L[ℝ] L2) (vector : L2) (fixed : operator vector = vector) (steps : ℕ) :
    (operator ^ steps) vector = vector := by
  simpa using continuousLinearMap_power_eigenvector_completion operator vector 1 (by simpa using fixed) steps

variable [PartialOrder L2]

theorem continuousLinearMap_power_positive_completion
    (operator : L2 →L[ℝ] L2) (positive : ∀ value, 0 ≤ value → 0 ≤ operator value)
    (value : L2) (nonnegative : 0 ≤ value) (steps : ℕ) : 0 ≤ (operator ^ steps) value := by
  induction steps with
  | zero => simpa using nonnegative
  | succ steps inductionHypothesis =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact positive _ inductionHypothesis

end
end IGSIII34.Spectral

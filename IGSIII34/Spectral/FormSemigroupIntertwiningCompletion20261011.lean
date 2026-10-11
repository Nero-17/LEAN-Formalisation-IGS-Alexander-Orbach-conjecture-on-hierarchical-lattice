import IGSIII34.Spectral.SemigroupContinuityCompletion20261011
import IGSIII34.Spectral.FormEigenvectorsImageCompletion20261011
import IGSIII34.Spectral.ActualContinuousKernelCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace Filter
open scoped Topology NNReal

variable {Energy L2 Index Target : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem continuousLinearMap_eq_on_hilbert_basis_target_completion20261011
    (basis : HilbertBasis Index ℝ Energy) (first second : Energy →L[ℝ] Target)
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

theorem form_semigroup_intertwining_completion20261011
    (formBasis : HilbertBasis Index ℝ Energy) (basis : HilbertBasis Index ℝ L2)
    (embedding : Energy →L[ℝ] L2) (coefficient : Index → ℝ)
    (basisImage : ∀ index, embedding (formBasis index) = coefficient index • basis index)
    (eigenvalues : Index → ℝ) (nonnegative : ∀ index, 0 ≤ eigenvalues index) (time : ℝ≥0) :
    embedding.comp (spectralL2SemigroupCompletion20261011 formBasis eigenvalues nonnegative time) =
      (spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative time).comp embedding := by
  apply continuousLinearMap_eq_on_hilbert_basis_target_completion20261011 formBasis
  intro index
  simp only [ContinuousLinearMap.comp_apply, spectralL2Semigroup_basis_completion20261011, map_smul, basisImage, smul_smul]
  rw [mul_comm]

theorem form_semigroup_continuous_representative_completion20261011
    (formBasis : HilbertBasis Index ℝ Energy) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (embedding : Energy →L[ℝ] Target)
    (potential : Energy) :
    Continuous (fun time : ℝ≥0 => embedding (spectralL2SemigroupCompletion20261011 formBasis eigenvalues nonnegative time potential)) :=
  embedding.continuous.comp (spectralL2Semigroup_continuous_completion20261011 formBasis eigenvalues nonnegative potential)

end
end IGSIII34.Spectral

import IGSIII34.Spectral.IndexedHeatSeriesCompletion
import IGSIII34.Spectral.HilbertEvaluation
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact

/-! Uniformly continuous heat series and the evaluation identity from a
constructed energy Hilbert basis. The eigenfunctions are continuous energy
potentials, with their normalization fixed by the resolvent eigenvalues. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace Filter
open scoped Topology

variable {Energy Space Index : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [TopologicalSpace Space] [CompactSpace Space]

def continuousFormEvaluationCompletion
    (embedding : Energy →L[ℝ] C(Space, ℝ)) (point : Space) : StrongDual ℝ Energy :=
  (ContinuousMap.evalCLM (R := ℝ) point).comp embedding

theorem continuousFormEvaluation_norm_le_completion
    (embedding : Energy →L[ℝ] C(Space, ℝ)) (point : Space) :
    ‖continuousFormEvaluationCompletion embedding point‖ ≤ ‖embedding‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg embedding)
  intro potential
  exact (ContinuousMap.norm_coe_le_norm (embedding potential) point).trans (embedding.le_opNorm potential)

def continuousResolventEigenfunctionsCompletion
    (embedding : Energy →L[ℝ] C(Space, ℝ)) (basis : HilbertBasis Index ℝ Energy)
    (eigenvalues : Index → ℝ) (index : Index) : C(Space, ℝ) :=
  (Real.sqrt (eigenvalues index))⁻¹ • embedding (basis index)

theorem continuousResolventEigenfunctions_weight_identity_completion
    (embedding : Energy →L[ℝ] C(Space, ℝ)) (basis : HilbertBasis Index ℝ Energy)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (index : Index) (point : Space) :
    continuousResolventEigenfunctionsCompletion embedding basis eigenvalues index point ^ 2 /
      (1 + ((eigenvalues index)⁻¹ - 1)) =
        continuousFormEvaluationCompletion embedding point (basis index) ^ 2 := by
  change ((Real.sqrt (eigenvalues index))⁻¹ * embedding (basis index) point) ^ 2 /
    (1 + ((eigenvalues index)⁻¹ - 1)) = (embedding (basis index) point) ^ 2
  have square := Real.sq_sqrt (positive index).le
  have nonzero := (Real.sqrt_pos.mpr (positive index)).ne'
  have valueNonzero := (positive index).ne'
  have denominator : 1 + ((eigenvalues index)⁻¹ - 1) = (eigenvalues index)⁻¹ := by ring
  rw [denominator]
  field_simp
  rw [square]
  ring

theorem continuousResolventEigenfunctions_evaluation_parseval_completion
    (embedding : Energy →L[ℝ] C(Space, ℝ)) (basis : HilbertBasis Index ℝ Energy)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (point : Space) :
    HasSum (fun index =>
      continuousResolventEigenfunctionsCompletion embedding basis eigenvalues index point ^ 2 /
        (1 + ((eigenvalues index)⁻¹ - 1)))
      (‖continuousFormEvaluationCompletion embedding point‖ ^ 2) := by
  simp only [continuousResolventEigenfunctions_weight_identity_completion embedding basis eigenvalues positive]
  exact hilbert_basis_evaluation_parseval basis _

theorem continuousResolventEigenfunctions_evaluation_bound_completion
    (embedding : Energy →L[ℝ] C(Space, ℝ)) (basis : HilbertBasis Index ℝ Energy)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (point : Space) (indices : Finset Index) :
    ∑ index ∈ indices,
      continuousResolventEigenfunctionsCompletion embedding basis eigenvalues index point ^ 2 /
        (1 + ((eigenvalues index)⁻¹ - 1)) ≤ ‖embedding‖ ^ 2 := by
  simp only [continuousResolventEigenfunctions_weight_identity_completion embedding basis eigenvalues positive]
  apply (finite_orthonormal_evaluation_bound basis basis.orthonormal _ indices).trans
  nlinarith [continuousFormEvaluation_norm_le_completion embedding point,
    norm_nonneg embedding, norm_nonneg (continuousFormEvaluationCompletion embedding point)]

theorem continuousResolventEigenfunctions_heat_kernel_continuousOn_completion
    (embedding : Energy →L[ℝ] C(Space, ℝ)) (basis : HilbertBasis Index ℝ Energy)
    (eigenvalues : Index → ℝ) (positive : ∀ index, 0 < eigenvalues index)
    (generatorNonnegative : ∀ index, 0 ≤ (eigenvalues index)⁻¹ - 1)
    (diverge : Tendsto (fun index => (eigenvalues index)⁻¹ - 1) cofinite atTop) :
    ContinuousOn (fun point : ℝ × Space × Space =>
      indexedSpectralHeatKernelCompletion (fun index => (eigenvalues index)⁻¹ - 1)
        (fun index => continuousResolventEigenfunctionsCompletion embedding basis eigenvalues index)
        point.1 point.2.1 point.2.2) {point | 0 < point.1} := by
  apply indexed_spectral_heat_kernel_continuousOn_completion _ _
    (fun index => (continuousResolventEigenfunctionsCompletion embedding basis eigenvalues index).continuous)
    generatorNonnegative diverge (‖embedding‖ ^ 2) (sq_nonneg _)
  exact continuousResolventEigenfunctions_evaluation_bound_completion embedding basis eigenvalues positive

end
end IGSIII34.Spectral

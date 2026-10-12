import IGSIII34.Spectral.FormEigenbasisCompletion

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace

variable {Energy L2 Index : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

theorem resolventEnergyHilbertBasis_apply_completion
    (embedding : Energy →L[ℝ] L2) (injective : Function.Injective embedding)
    (solution : L2 →L[ℝ] Energy)
    (variational : ∀ forcing test, inner ℝ (solution forcing) test = inner ℝ forcing (embedding test))
    (basis : HilbertBasis Index ℝ L2) (eigenvalues : Index → ℝ)
    (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, embedding (solution (basis index)) = eigenvalues index • basis index)
    (index : Index) :
    resolventEnergyHilbertBasisCompletion embedding injective solution variational
      basis eigenvalues positive eigenvectors index =
        normalisedResolventEigenvectorsCompletion solution basis eigenvalues index :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) index

theorem resolventEnergyHilbertBasis_embedding_completion
    (embedding : Energy →L[ℝ] L2) (injective : Function.Injective embedding)
    (solution : L2 →L[ℝ] Energy)
    (variational : ∀ forcing test, inner ℝ (solution forcing) test = inner ℝ forcing (embedding test))
    (basis : HilbertBasis Index ℝ L2) (eigenvalues : Index → ℝ)
    (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, embedding (solution (basis index)) = eigenvalues index • basis index)
    (index : Index) :
    embedding (resolventEnergyHilbertBasisCompletion embedding injective solution variational
      basis eigenvalues positive eigenvectors index) = Real.sqrt (eigenvalues index) • basis index := by
  rw [resolventEnergyHilbertBasis_apply_completion]
  simp only [normalisedResolventEigenvectorsCompletion, map_smul, eigenvectors, smul_smul]
  have scalar : (Real.sqrt (eigenvalues index))⁻¹ * eigenvalues index = Real.sqrt (eigenvalues index) := by
    have square := Real.sq_sqrt (positive index).le
    have nonzero := (Real.sqrt_pos.mpr (positive index)).ne'
    field_simp
    nlinarith
  rw [scalar]

end
end IGSIII34.Spectral

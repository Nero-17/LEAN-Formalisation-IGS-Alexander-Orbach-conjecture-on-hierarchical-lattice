import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace

variable {Source Target Index : Type*}
  [NormedAddCommGroup Source] [InnerProductSpace ℝ Source] [CompleteSpace Source]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem continuousLinearMap_eq_of_Hilbert_basis_completion
    (basis : HilbertBasis Index ℝ Source) (first second : Source →L[ℝ] Target)
    (equalOnBasis : ∀ index, first (basis index) = second (basis index)) : first = second := by
  apply ContinuousLinearMap.ext
  intro value
  have firstSum := (basis.hasSum_repr value).mapL first
  have secondSum := (basis.hasSum_repr value).mapL second
  have terms : (fun index => first (basis.repr value index • basis index)) =
      (fun index => second (basis.repr value index • basis index)) := by
    funext index
    simp only [map_smul, equalOnBasis]
  rw [terms] at firstSum
  exact firstSum.unique secondSum
end
end IGSIII34.Spectral

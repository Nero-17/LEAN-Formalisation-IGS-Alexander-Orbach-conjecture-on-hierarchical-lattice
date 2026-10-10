import Universality.Matrix.TwoByTwo
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# A spectral obstruction detected by trace

These results use mathlib's spectrum, not a substitute definition.  They are
independent of the existence theorem for positive Perron eigenvectors.
-/

namespace Universality

theorem twoByTwo_spectral_equation {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) {root : K} (h : root ∈ spectrum K A) :
    root ^ 2 - A.trace * root + A.det = 0 := by
  have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp h
  simpa [Polynomial.IsRoot, Matrix.charpoly_fin_two] using hroot

theorem twoByTwo_spectra_disjoint {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = B.det) (hne : A.det ≠ 0) (htrace : A.trace ≠ B.trace) :
    Disjoint (spectrum K A) (spectrum K B) := by
  apply Set.disjoint_left.mpr
  intro root hA hB
  have h₁ := twoByTwo_spectral_equation A hA
  have h₂ := twoByTwo_spectral_equation B hB
  rw [← hdet] at h₂
  have hr : root ≠ 0 := by
    intro hz
    subst root
    exact hne (by simpa using h₁)
  exact htrace (quadratic_trace_eq_of_common_nonzero_root hr h₁ h₂)

theorem noncommutative_rational_spectra_disjoint :
    Disjoint (spectrum ℚ (wheatstoneBlock ^ 2 * oppositeWheatstoneBlock ^ 2))
      (spectrum ℚ (wheatstoneBlock * oppositeWheatstoneBlock *
        wheatstoneBlock * oppositeWheatstoneBlock)) :=
  twoByTwo_spectra_disjoint _ _ noncommutative_determinants_eq
    noncommutative_determinant_ne_zero noncommutative_traces_ne

/-- The separation persists over every characteristic-zero field, so the
rational computation also separates the real and complex spectra. -/
theorem noncommutative_spectra_disjoint (K : Type*) [Field K] [CharZero K] :
    Disjoint
      (spectrum K ((Rat.castHom K).mapMatrix
        (wheatstoneBlock ^ 2 * oppositeWheatstoneBlock ^ 2)))
      (spectrum K ((Rat.castHom K).mapMatrix
        (wheatstoneBlock * oppositeWheatstoneBlock *
          wheatstoneBlock * oppositeWheatstoneBlock))) := by
  apply twoByTwo_spectra_disjoint
  · rw [← RingHom.map_det, ← RingHom.map_det,
      noncommutative_determinants_eq]
  · rw [← RingHom.map_det]
    intro h
    apply noncommutative_determinant_ne_zero
    apply (Rat.castHom K).injective
    simpa only [map_zero] using h
  · intro h
    apply noncommutative_traces_ne
    apply (Rat.castHom K).injective
    simpa only [AddMonoidHom.map_trace, RingHom.mapMatrix_apply] using h

end Universality

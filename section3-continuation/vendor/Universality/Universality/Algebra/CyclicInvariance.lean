import Universality.Matrix.PositiveEigenvector
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Cyclic invariance of the algebraic data

Cyclically changing two consecutive blocks preserves the characteristic
polynomial and actual spectral radius.  This does not assert arbitrary
permutation invariance, which is disproved in NoncommutativeExample.
-/

namespace Universality

theorem cyclic_spectrum_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (A B : Matrix ι ι K) :
    spectrum K (A * B) = spectrum K (B * A) := by
  ext root
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_mul_comm A B]

theorem cyclic_spectralRadius_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    spectralRadius ℂ (A * B) = spectralRadius ℂ (B * A) := by
  unfold spectralRadius
  rw [cyclic_spectrum_eq]

theorem cyclic_word_spectralRadius_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (first second : List (Matrix ι ι ℂ)) :
    spectralRadius ℂ (first ++ second).prod = spectralRadius ℂ (second ++ first).prod := by
  rw [List.prod_append, List.prod_append, cyclic_spectralRadius_eq]

theorem cyclic_fixed_point (f g : ℝ → ℝ) (p : ℝ) (h : f (g p) = p) :
    g (f (g p)) = g p := congrArg g h

theorem cyclic_derivative_multiplier (f g : ℝ → ℝ) (p fderiv gderiv : ℝ)
    (hfixed : f (g p) = p) (hf : HasDerivAt f fderiv (g p))
    (hg : HasDerivAt g gderiv p) :
    HasDerivAt (fun x => f (g x)) (fderiv * gderiv) p ∧
      HasDerivAt (fun x => g (f x)) (fderiv * gderiv) (g p) := by
  constructor
  · exact hf.comp p hg
  · have hg' : HasDerivAt g gderiv (f (g p)) := by rwa [hfixed]
    rw [mul_comm fderiv gderiv]
    exact hg'.comp (g p) hf

end Universality

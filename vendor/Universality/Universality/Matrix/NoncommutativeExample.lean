import Universality.Matrix.PositiveTwoByTwo

/-!
# Exact noncommutative spectral growth

The field embedding of the computed rational products is explicit.  This file
proves unequal actual complex spectral radii and unequal logarithmic growth at
scale 36.  The finite-network and substitution bridges are separate modules.
-/

namespace Universality
noncomputable section

def groupedMassBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  (Rat.castHom ℝ).mapMatrix (wheatstoneBlock ^ 2 * oppositeWheatstoneBlock ^ 2)

def alternatingMassBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  (Rat.castHom ℝ).mapMatrix
    (wheatstoneBlock * oppositeWheatstoneBlock * wheatstoneBlock * oppositeWheatstoneBlock)

theorem groupedMassBlock_pos (i j : Fin 2) : 0 < groupedMassBlock i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [groupedMassBlock, wheatstoneBlock, oppositeWheatstoneBlock,
      pow_two, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem alternatingMassBlock_pos (i j : Fin 2) : 0 < alternatingMassBlock i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [alternatingMassBlock, wheatstoneBlock, oppositeWheatstoneBlock,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem positiveRoot_mem_real_spectrum (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) : positiveRoot A ∈ spectrum ℝ A := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  simpa [Polynomial.IsRoot, Matrix.charpoly_fin_two] using positiveRoot_quadratic A hA

theorem noncommutative_positiveRoots_ne :
    positiveRoot groupedMassBlock ≠ positiveRoot alternatingMassBlock := by
  intro heq
  have hdisjoint := noncommutative_spectra_disjoint ℝ
  apply Set.disjoint_left.mp hdisjoint
  · exact positiveRoot_mem_real_spectrum groupedMassBlock groupedMassBlock_pos
  · rw [heq]
    exact positiveRoot_mem_real_spectrum alternatingMassBlock alternatingMassBlock_pos

theorem noncommutative_complex_spectralRadii_ne :
    spectralRadius ℂ (groupedMassBlock.map Complex.ofReal) ≠
      spectralRadius ℂ (alternatingMassBlock.map Complex.ofReal) := by
  rw [spectralRadius_positive_twoByTwo _ groupedMassBlock_pos,
    spectralRadius_positive_twoByTwo _ alternatingMassBlock_pos]
  intro h
  apply noncommutative_positiveRoots_ne
  have h' := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (positiveRoot_pos _ groupedMassBlock_pos).le,
    ENNReal.toReal_ofReal (positiveRoot_pos _ alternatingMassBlock_pos).le] using h'

def logarithmicSpectralGrowth (A : Matrix (Fin 2) (Fin 2) ℝ) (scale : ℝ) : ℝ :=
  Real.log ((spectralRadius ℂ (A.map Complex.ofReal)).toReal) / Real.log scale

theorem noncommutative_logarithmic_growth_ne :
    logarithmicSpectralGrowth groupedMassBlock 36 ≠
      logarithmicSpectralGrowth alternatingMassBlock 36 := by
  unfold logarithmicSpectralGrowth
  rw [spectralRadius_positive_twoByTwo _ groupedMassBlock_pos,
    spectralRadius_positive_twoByTwo _ alternatingMassBlock_pos,
    ENNReal.toReal_ofReal (positiveRoot_pos _ groupedMassBlock_pos).le,
    ENNReal.toReal_ofReal (positiveRoot_pos _ alternatingMassBlock_pos).le]
  intro h
  have hlog : Real.log (positiveRoot groupedMassBlock) =
      Real.log (positiveRoot alternatingMassBlock) :=
    (div_left_inj' (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 36)))).mp h
  exact noncommutative_positiveRoots_ne
    (Real.log_injOn_pos (positiveRoot_pos _ groupedMassBlock_pos)
      (positiveRoot_pos _ alternatingMassBlock_pos) hlog)

end
end Universality

import Universality.Matrix.OppositeWheatstoneSpectrum
import Universality.Matrix.NoncommutativeExample

namespace Universality
noncomputable section
open Matrix FiniteNetwork

def groupedFullMassMatrix : Matrix LiveState LiveState ℝ :=
  wheatstoneMassMatrix * wheatstoneMassMatrix *
    oppositeWheatstoneMassMatrix * oppositeWheatstoneMassMatrix

def alternatingFullMassMatrix : Matrix LiveState LiveState ℝ :=
  wheatstoneMassMatrix * oppositeWheatstoneMassMatrix *
    wheatstoneMassMatrix * oppositeWheatstoneMassMatrix

theorem matrix_product_nonneg {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ (A * B) i j := by
  intro i j
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hA i k) (hB k j)

theorem groupedFullMassMatrix_nonneg : ∀ σ τ, 0 ≤ groupedFullMassMatrix σ τ :=
  matrix_product_nonneg _ _
    (matrix_product_nonneg _ _
      (matrix_product_nonneg _ _
        (fun σ τ => (wheatstoneMassMatrix_pos σ τ).le)
        (fun σ τ => (wheatstoneMassMatrix_pos σ τ).le))
      (fun σ τ => (oppositeWheatstoneMassMatrix_pos σ τ).le))
    (fun σ τ => (oppositeWheatstoneMassMatrix_pos σ τ).le)

theorem alternatingFullMassMatrix_nonneg : ∀ σ τ, 0 ≤ alternatingFullMassMatrix σ τ :=
  matrix_product_nonneg _ _
    (matrix_product_nonneg _ _
      (matrix_product_nonneg _ _
        (fun σ τ => (wheatstoneMassMatrix_pos σ τ).le)
        (fun σ τ => (oppositeWheatstoneMassMatrix_pos σ τ).le))
      (fun σ τ => (wheatstoneMassMatrix_pos σ τ).le))
    (fun σ τ => (oppositeWheatstoneMassMatrix_pos σ τ).le)

theorem groupedFullMassMatrix_preserves : PreservesMassPlane groupedFullMassMatrix :=
  ((wheatstoneMassMatrix_preservesMassPlane.mul wheatstoneMassMatrix_preservesMassPlane).mul
    oppositeWheatstoneMassMatrix_preservesMassPlane).mul oppositeWheatstoneMassMatrix_preservesMassPlane

theorem alternatingFullMassMatrix_preserves : PreservesMassPlane alternatingFullMassMatrix :=
  ((wheatstoneMassMatrix_preservesMassPlane.mul oppositeWheatstoneMassMatrix_preservesMassPlane).mul
    wheatstoneMassMatrix_preservesMassPlane).mul oppositeWheatstoneMassMatrix_preservesMassPlane

theorem groupedFullMassMatrix_block : massPlaneBlock groupedFullMassMatrix = groupedMassBlock := by
  unfold groupedFullMassMatrix groupedMassBlock
  rw [massPlaneBlock_mul _ _ oppositeWheatstoneMassMatrix_preservesMassPlane,
    massPlaneBlock_mul _ _ oppositeWheatstoneMassMatrix_preservesMassPlane,
    massPlaneBlock_mul _ _ wheatstoneMassMatrix_preservesMassPlane,
    wheatstoneMassMatrix_block, oppositeWheatstoneMassMatrix_block]
  simp only [RingHom.mapMatrix_apply, pow_two, Matrix.map_mul, mul_assoc]

theorem alternatingFullMassMatrix_block :
    massPlaneBlock alternatingFullMassMatrix = alternatingMassBlock := by
  unfold alternatingFullMassMatrix alternatingMassBlock
  rw [massPlaneBlock_mul _ _ oppositeWheatstoneMassMatrix_preservesMassPlane,
    massPlaneBlock_mul _ _ wheatstoneMassMatrix_preservesMassPlane,
    massPlaneBlock_mul _ _ oppositeWheatstoneMassMatrix_preservesMassPlane,
    wheatstoneMassMatrix_block, oppositeWheatstoneMassMatrix_block]
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul]

theorem groupedFullMassMatrix_spectralRadius :
    spectralRadius ℂ (groupedFullMassMatrix.map Complex.ofReal) =
      ENNReal.ofReal (positiveRoot groupedMassBlock) := by
  rw [← groupedFullMassMatrix_block]
  apply massPlane_spectralRadius _ groupedFullMassMatrix_nonneg groupedFullMassMatrix_preserves
  rw [groupedFullMassMatrix_block]
  exact groupedMassBlock_pos

theorem alternatingFullMassMatrix_spectralRadius :
    spectralRadius ℂ (alternatingFullMassMatrix.map Complex.ofReal) =
      ENNReal.ofReal (positiveRoot alternatingMassBlock) := by
  rw [← alternatingFullMassMatrix_block]
  apply massPlane_spectralRadius _ alternatingFullMassMatrix_nonneg alternatingFullMassMatrix_preserves
  rw [alternatingFullMassMatrix_block]
  exact alternatingMassBlock_pos

theorem noncommutative_full_spectralRadii_ne :
    spectralRadius ℂ (groupedFullMassMatrix.map Complex.ofReal) ≠
      spectralRadius ℂ (alternatingFullMassMatrix.map Complex.ofReal) := by
  rw [groupedFullMassMatrix_spectralRadius, alternatingFullMassMatrix_spectralRadius]
  intro h
  apply noncommutative_positiveRoots_ne
  have hreal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (positiveRoot_pos _ groupedMassBlock_pos).le,
    ENNReal.toReal_ofReal (positiveRoot_pos _ alternatingMassBlock_pos).le] using hreal

end
end Universality

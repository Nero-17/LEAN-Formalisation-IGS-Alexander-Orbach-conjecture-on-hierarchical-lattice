import IGSIII4.SpectralDensity.ActualMomentFiniteLaw
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality IGSIII34.Probability IGSIII34.Percolation

theorem weightedCell_centered_second_moment {Outcome : Type*} [Fintype Outcome]
    (blocks paths interior : ℕ) (probability : ℝ)
    (probabilityPositive : 0 < probability) (probabilityBelowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability)
    (weight response : Outcome → ℝ) (normalized : ∑ outcome, weight outcome = 1) :
    weightedCellObservable blocks paths interior probability weight response
        (fun value => (value - weightedCellMean blocks paths interior probability weight response) ^ 2) =
      weightedCellSecondMoment blocks paths interior probability weight response -
        weightedCellMean blocks paths interior probability weight response ^ 2 := by
  have cellNormalized : ∑ configuration,
      (network blocks paths interior).conditionalCellWeight probability true configuration = 1 :=
    (network blocks paths interior).sum_conditionalCellWeight probability
      (by rwa [critical]) (by rwa [critical]) true
  have productNormalized : ∑ input : Fin (Fintype.card (Edge blocks paths interior)) → Outcome,
      productWeight weight input = 1 := sum_productWeight weight normalized
  have identity := finiteVariance_eq_second_moment
    (fun outcome : (Fin (Fintype.card (Edge blocks paths interior)) → Bool) ×
      (Fin (Fintype.card (Edge blocks paths interior)) → Outcome) =>
      (network blocks paths interior).conditionalCellWeight probability true outcome.1 *
        productWeight weight outcome.2)
    (fun outcome => electricalCell (network blocks paths interior) outcome.1
      (fun edge => response (outcome.2 edge)))
    (product_weight_normalized _ _ cellNormalized productNormalized)
  simpa only [weightedCellObservable, weightedCellMean, weightedCellSecondMoment,
    finiteVariance, finiteMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, id_eq] using identity

end
end IGSIII4.SpectralDensity.ActualFamily

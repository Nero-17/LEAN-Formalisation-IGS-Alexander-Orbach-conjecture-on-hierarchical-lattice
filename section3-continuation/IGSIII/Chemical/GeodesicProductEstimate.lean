import IGSIII.Chemical.GeodesicLength
import Universality.Percolation.ProductDisintegration

/-! Finite product variance decay inputs with explicit edge-count dependence. -/

set_option autoImplicit false

namespace IGSIII.Chemical

open IGSIII.Probability PathFamily
open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome] {count : ℕ}

theorem finiteMean_tuple_local (weight : Fin count → Outcome → ℝ)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (edge : Fin count) (response : Outcome → ℝ) :
    finiteMean (tupleWeight weight) (fun outcome => response (outcome edge)) =
      finiteMean (weight edge) response := by
  unfold finiteMean tupleWeight
  rw [Universality.finite_product_local_moment]
  simp only [normalized, Finset.prod_const_one, one_mul]

theorem finiteMean_tuple_sum_local (weight response : Fin count → Outcome → ℝ)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1) :
    finiteMean (tupleWeight weight) (fun outcome => ∑ edge, response edge (outcome edge)) =
      ∑ edge, finiteMean (weight edge) (response edge) := by
  unfold finiteMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun edge _ => finiteMean_tuple_local weight normalized edge (response edge))

theorem finiteMean_geodesic_card_le_product_inverse_moment
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (positive : ∀ edge outcome, 0 < localCost edge outcome)
    (inverseMoment : ℝ) (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (inverseMomentBound : ∀ edge,
      finiteMean (weight edge) (fun outcome => (localCost edge outcome)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean (tupleWeight weight)
      (fun outcome => ((family.minimizingPath (sampledEdgeCost localCost outcome)).card : ℝ)) ≤
      (finiteMean (tupleWeight weight)
        (fun outcome => family.shortest (sampledEdgeCost localCost outcome) ^ 2)) ^ (1 / (2 : ℝ)) *
          ((count : ℝ) * inverseMoment) ^ (1 / power) := by
  have inverseNonnegative : 0 ≤ finiteMean (tupleWeight weight)
      (fun outcome => ∑ edge, (localCost edge (outcome edge))⁻¹ ^ power) := by
    unfold finiteMean
    apply Finset.sum_nonneg
    intro outcome _
    exact mul_nonneg (tupleWeight_nonnegative weight weightNonnegative outcome)
      (Finset.sum_nonneg (fun edge _ => Real.rpow_nonneg (inv_nonneg.mpr (positive edge (outcome edge)).le) _))
  have inverseBound : finiteMean (tupleWeight weight)
      (fun outcome => ∑ edge, (localCost edge (outcome edge))⁻¹ ^ power) ≤
        (count : ℝ) * inverseMoment := by
    rw [finiteMean_tuple_sum_local weight (fun edge outcome => (localCost edge outcome)⁻¹ ^ power) normalized]
    calc
      _ ≤ ∑ _edge : Fin count, inverseMoment := Finset.sum_le_sum (fun edge _ => inverseMomentBound edge)
      _ = _ := by simp
  refine (finiteMean_geodesic_card_le_inverse_moment family (tupleWeight weight)
    (sampledEdgeCost localCost) powerAtLeastTwo
    (tupleWeight_nonnegative weight weightNonnegative) (tupleWeight_normalized weight normalized)
    (fun outcome edge => positive edge (outcome edge))).trans ?_
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow inverseNonnegative inverseBound (by
      have : 0 < power := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) powerAtLeastTwo
      positivity))
    (Real.rpow_nonneg (Finset.sum_nonneg (fun outcome _ =>
      mul_nonneg (tupleWeight_nonnegative weight weightNonnegative outcome) (sq_nonneg _))) _)

theorem shortest_variance_le_product_moment_bound
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (positive : ∀ edge outcome, 0 < localCost edge outcome)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ edge,
      finiteMean (weight edge) (fun outcome => localCost edge outcome ^ 2) ≤ secondMoment)
    (inverseMomentBound : ∀ edge,
      finiteMean (weight edge) (fun outcome => (localCost edge outcome)⁻¹ ^ power) ≤ inverseMoment) :
    finiteVariance (tupleWeight weight)
      (fun outcome => family.shortest (sampledEdgeCost localCost outcome)) ≤
      2 * secondMoment *
        (finiteMean (tupleWeight weight)
          (fun outcome => family.shortest (sampledEdgeCost localCost outcome) ^ 2)) ^ (1 / (2 : ℝ)) *
            ((count : ℝ) * inverseMoment) ^ (1 / power) := by
  refine (shortest_variance_le_geodesic_length family weight localCost weightNonnegative normalized
    (fun edge outcome => (positive edge outcome).le) secondMoment secondMomentBound).trans ?_
  have bound := finiteMean_geodesic_card_le_product_inverse_moment family weight localCost
    powerAtLeastTwo weightNonnegative normalized positive inverseMoment inverseMomentNonnegative inverseMomentBound
  exact (mul_le_mul_of_nonneg_left bound (mul_nonneg (by norm_num) secondMomentNonnegative)).trans_eq (by ring)

end IGSIII.Chemical

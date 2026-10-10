import IGSIII.Chemical.SubstitutionPaths.ConditionalVariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped BigOperators

theorem finiteMean_scale {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (factor : ℝ) :
    finiteMean weight (fun outcome => factor * response outcome) = factor * finiteMean weight response := by
  simp only [finiteMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

theorem finiteVariance_scale {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (factor : ℝ) :
    finiteVariance weight (fun outcome => factor * response outcome) = factor ^ 2 * finiteVariance weight response := by
  unfold finiteVariance
  rw [finiteMean_scale]
  simp only [← mul_sub, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

theorem actual_substitution_normalized_conditional_variance_bound
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (outerFixedPoint : outer.reliability p = p) (innerFixedPoint : inner.reliability p = p)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : normalizedDistanceMoment inner p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean (inner.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance inner p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean (outer.conditionalCellWeight p true) (fun coarse =>
      finiteVariance (tupleWeight (fun edge => inner.conditionalCellWeight p (coarse edge)))
        (fun cells => cellMinPlus outer inner coarse cells / conditionedDistanceMean (outer.substitute inner) p)) ≤
      2 * secondMoment * Real.sqrt (normalizedDistanceMoment (outer.substitute inner) p 2) *
        ((outerEdges : ℝ) * inverseMoment) ^ (1 / power) *
          (conditionedDistanceMean inner p / conditionedDistanceMean (outer.substitute inner) p) := by
  have innerMeanPositive : 0 < conditionedDistanceMean inner p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne inner positive.le lessOne.le
      (by rwa [innerFixedPoint]) (by rwa [innerFixedPoint]))
  have parentFixedPoint : (outer.substitute inner).reliability p = p := by
    rw [substitute_reliability, innerFixedPoint, outerFixedPoint]
  have parentMeanPositive : 0 < conditionedDistanceMean (outer.substitute inner) p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [parentFixedPoint]) (by rwa [parentFixedPoint]))
  have scaledCell (coarse : Configuration outerEdges) (cells : Fin outerEdges → Configuration innerEdges) :
      cellMinPlus outer inner coarse cells / conditionedDistanceMean (outer.substitute inner) p =
        (conditionedDistanceMean inner p / conditionedDistanceMean (outer.substitute inner) p) *
          (cellMinPlus outer inner coarse cells / conditionedDistanceMean inner p) := by
    field_simp
  have scaledDistance (configuration : Configuration (outerEdges * innerEdges)) :
      (((outer.substitute inner).openGraph configuration).dist
        (outer.substitute inner).source (outer.substitute inner).target : ℝ) /
          conditionedDistanceMean inner p =
      (conditionedDistanceMean (outer.substitute inner) p / conditionedDistanceMean inner p) *
        normalizedDistance (outer.substitute inner) p configuration := by
    unfold normalizedDistance
    field_simp
  have secondEquality :
      finiteMean ((outer.substitute inner).conditionalCellWeight p true) (fun configuration =>
        ((((outer.substitute inner).openGraph configuration).dist
          (outer.substitute inner).source (outer.substitute inner).target : ℝ) /
            conditionedDistanceMean inner p) ^ 2) =
        (conditionedDistanceMean (outer.substitute inner) p / conditionedDistanceMean inner p) ^ 2 *
          normalizedDistanceMoment (outer.substitute inner) p 2 := by
    simp_rw [scaledDistance, mul_pow]
    exact finiteMean_scale _ _ _
  have bound := actual_substitution_conditional_variance_bound outer inner simple p positive lessOne
    outerFixedPoint innerFixedPoint powerAtLeastTwo secondMoment inverseMoment
    secondMomentNonnegative inverseMomentNonnegative secondMomentBound inverseMomentBound
  rw [secondEquality, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (div_nonneg parentMeanPositive.le innerMeanPositive.le)] at bound
  simp_rw [scaledCell, finiteVariance_scale]
  rw [finiteMean_scale]
  refine (mul_le_mul_of_nonneg_left bound (sq_nonneg _)).trans_eq ?_
  field_simp
  <;> ring

end IGSIII.Chemical.Substitution

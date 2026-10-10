import IGSIII.Chemical.GeodesicVariance

/-! The geodesic variance bound uses only the second moment of a fresh edge.
The finite Efron--Stein constant used here is two. -/

set_option autoImplicit false

namespace IGSIII.Chemical

open IGSIII.Probability PathFamily
open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome] {count : ℕ}

theorem PathFamily.shortest_update_sq_le_fresh_geodesic_cost
    (family : PathFamily (Fin count)) (cost : Fin count → ℝ)
    (nonnegative : ∀ edge, 0 ≤ cost edge) (changed : Fin count) (replacement : ℝ)
    (replacementNonnegative : 0 ≤ replacement) :
    (family.shortest (Function.update cost changed replacement) - family.shortest cost) ^ 2 ≤
      replacement ^ 2 * (if changed ∈ family.minimizingPath cost then (1 : ℝ) else 0) +
        cost changed ^ 2 * (if changed ∈ family.minimizingPath
          (Function.update cost changed replacement) then (1 : ℝ) else 0) := by
  have forward := family.shortest_update_sub_le_geodesic cost changed replacement
  have backward := family.shortest_update_sub_le_geodesic
    (Function.update cost changed replacement) changed (cost changed)
  have restored : Function.update (Function.update cost changed replacement) changed (cost changed) = cost := by
    funext edge
    by_cases equal : edge = changed <;> simp [equal]
  simp only [restored, Function.update_self] at backward
  by_cases increase : family.shortest cost ≤ family.shortest (Function.update cost changed replacement)
  · have lower : 0 ≤ family.shortest (Function.update cost changed replacement) - family.shortest cost := sub_nonneg.mpr increase
    by_cases oldMember : changed ∈ family.minimizingPath cost
    · simp only [if_pos oldMember, mul_one] at forward ⊢
      have bound : family.shortest (Function.update cost changed replacement) - family.shortest cost ≤ replacement := by
        linarith [nonnegative changed]
      have squared := pow_le_pow_left₀ lower bound 2
      exact squared.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)))
    · simp only [if_neg oldMember, mul_zero] at forward ⊢
      have zeroDifference : family.shortest (Function.update cost changed replacement) - family.shortest cost = 0 := le_antisymm forward lower
      rw [zeroDifference, zero_pow (by decide), zero_add]
      exact mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)
  · have lower : 0 ≤ family.shortest cost - family.shortest (Function.update cost changed replacement) := sub_nonneg.mpr (le_of_not_ge increase)
    by_cases newMember : changed ∈ family.minimizingPath (Function.update cost changed replacement)
    · simp only [if_pos newMember, mul_one] at backward ⊢
      have bound : family.shortest cost - family.shortest (Function.update cost changed replacement) ≤ cost changed := by linarith
      have squared := pow_le_pow_left₀ lower bound 2
      have symmetry : (family.shortest (Function.update cost changed replacement) - family.shortest cost) ^ 2 =
          (family.shortest cost - family.shortest (Function.update cost changed replacement)) ^ 2 := by ring
      rw [symmetry]
      exact squared.trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)))
    · simp only [if_neg newMember, mul_zero] at backward ⊢
      have zeroDifference : family.shortest cost - family.shortest (Function.update cost changed replacement) = 0 := le_antisymm backward lower
      have zeroForward : family.shortest (Function.update cost changed replacement) - family.shortest cost = 0 := by linarith
      rw [zeroForward, zero_pow (by decide), add_zero]
      exact mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)

noncomputable def freshGeodesicCost (family : PathFamily (Fin count))
    (localCost : Fin count → Outcome → ℝ) (changed : Fin count)
    (outcome : Fin count → Outcome) (replacement : Outcome) : ℝ :=
  localCost changed replacement ^ 2 *
    if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then 1 else 0

theorem fresh_geodesic_cost_exchange
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    (changed : Fin count) :
    finiteMean (tupleWeight weight) (fun outcome => finiteMean (weight changed)
      (freshGeodesicCost family localCost changed outcome)) =
      finiteMean (tupleWeight weight) (fun outcome => finiteMean (weight changed)
        (fun replacement => localCost changed (outcome changed) ^ 2 *
          if changed ∈ family.minimizingPath
            (sampledEdgeCost localCost (Function.update outcome changed replacement)) then 1 else 0)) := by
  have exchange := finiteMean_resampling_exchange weight changed
    (fun pair => freshGeodesicCost family localCost changed pair.1 pair.2)
  change finiteMean (fun pair : (Fin count → Outcome) × Outcome =>
    tupleWeight weight pair.1 * weight changed pair.2)
      (fun pair => freshGeodesicCost family localCost changed pair.1 pair.2) =
    finiteMean (fun pair : (Fin count → Outcome) × Outcome =>
      tupleWeight weight pair.1 * weight changed pair.2)
      (fun pair => freshGeodesicCost family localCost changed
        (Function.update pair.1 changed pair.2) (pair.1 changed)) at exchange
  rw [finiteMean_product (tupleWeight weight) (weight changed)
    (freshGeodesicCost family localCost changed)] at exchange
  rw [finiteMean_product (tupleWeight weight) (weight changed)
    (fun outcome replacement => freshGeodesicCost family localCost changed
      (Function.update outcome changed replacement) (outcome changed))] at exchange
  exact exchange

theorem shortest_variance_le_fresh_geodesic_second_moments
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (costNonnegative : ∀ edge outcome, 0 ≤ localCost edge outcome) :
    finiteVariance (tupleWeight weight)
      (fun outcome => family.shortest (sampledEdgeCost localCost outcome)) ≤
        2 * finiteMean (tupleWeight weight) (fun outcome => ∑ changed,
          finiteMean (weight changed) (fun replacement => localCost changed replacement ^ 2) *
            if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then 1 else 0) := by
  have pointwise (outcome : Fin count → Outcome) (changed : Fin count) (replacement : Outcome) :
      (family.shortest (sampledEdgeCost localCost outcome) -
        family.shortest (sampledEdgeCost localCost (Function.update outcome changed replacement))) ^ 2 ≤
      freshGeodesicCost family localCost changed outcome replacement +
        localCost changed (outcome changed) ^ 2 *
          if changed ∈ family.minimizingPath
            (sampledEdgeCost localCost (Function.update outcome changed replacement)) then 1 else 0 := by
    have bound := family.shortest_update_sq_le_fresh_geodesic_cost
      (sampledEdgeCost localCost outcome) (fun edge => costNonnegative edge (outcome edge))
      changed (localCost changed replacement) (costNonnegative changed replacement)
    rw [← sampledEdgeCost_update] at bound
    change _ ≤ _ at bound
    have symmetry : (family.shortest (sampledEdgeCost localCost outcome) -
        family.shortest (sampledEdgeCost localCost (Function.update outcome changed replacement))) ^ 2 =
      (family.shortest (sampledEdgeCost localCost (Function.update outcome changed replacement)) -
        family.shortest (sampledEdgeCost localCost outcome)) ^ 2 := by ring
    rw [symmetry]
    exact bound
  have meanSum (response : Fin count → (Fin count → Outcome) → ℝ) :
      finiteMean (tupleWeight weight) (fun outcome => ∑ changed, response changed outcome) =
        ∑ changed, finiteMean (tupleWeight weight) (response changed) := by
    unfold finiteMean
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have freshMean (changed : Fin count) (outcome : Fin count → Outcome) :
      finiteMean (weight changed) (freshGeodesicCost family localCost changed outcome) =
        finiteMean (weight changed) (fun replacement => localCost changed replacement ^ 2) *
          if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then 1 else 0 := by
    simp only [finiteMean, freshGeodesicCost, ← mul_assoc, Finset.sum_mul]
  refine (finite_product_variance_le_resampling count weight weightNonnegative normalized _).trans ?_
  calc
    _ ≤ finiteMean (tupleWeight weight) (fun outcome => ∑ changed,
        finiteMean (weight changed) (fun replacement =>
          freshGeodesicCost family localCost changed outcome replacement +
            localCost changed (outcome changed) ^ 2 *
              if changed ∈ family.minimizingPath
                (sampledEdgeCost localCost (Function.update outcome changed replacement)) then 1 else 0)) := by
      unfold resamplingEnergy finiteMean
      apply Finset.sum_le_sum
      intro outcome _
      apply mul_le_mul_of_nonneg_left _ (tupleWeight_nonnegative weight weightNonnegative outcome)
      apply Finset.sum_le_sum
      intro changed _
      apply Finset.sum_le_sum
      intro replacement _
      exact mul_le_mul_of_nonneg_left (pointwise outcome changed replacement) (weightNonnegative changed replacement)
    _ = _ := by
      rw [meanSum]
      simp_rw [finiteMean_add]
      simp_rw [← fresh_geodesic_cost_exchange]
      simp_rw [freshMean]
      rw [meanSum]
      simp only [two_mul, Finset.sum_add_distrib]

theorem shortest_variance_le_geodesic_length
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    (weightNonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1)
    (costNonnegative : ∀ edge outcome, 0 ≤ localCost edge outcome)
    (secondMoment : ℝ)
    (secondMomentBound : ∀ edge,
      finiteMean (weight edge) (fun replacement => localCost edge replacement ^ 2) ≤ secondMoment) :
    finiteVariance (tupleWeight weight)
      (fun outcome => family.shortest (sampledEdgeCost localCost outcome)) ≤
        2 * secondMoment * finiteMean (tupleWeight weight)
          (fun outcome => ((family.minimizingPath (sampledEdgeCost localCost outcome)).card : ℝ)) := by
  refine (shortest_variance_le_fresh_geodesic_second_moments family weight localCost
    weightNonnegative normalized costNonnegative).trans ?_
  have indicatorSum (outcome : Fin count → Outcome) :
      (∑ changed, if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome)
        then (1 : ℝ) else 0) =
        ((family.minimizingPath (sampledEdgeCost localCost outcome)).card : ℝ) := by simp
  have bound : finiteMean (tupleWeight weight) (fun outcome => ∑ changed,
      finiteMean (weight changed) (fun replacement => localCost changed replacement ^ 2) *
        if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then 1 else 0) ≤
      secondMoment * finiteMean (tupleWeight weight)
        (fun outcome => ((family.minimizingPath (sampledEdgeCost localCost outcome)).card : ℝ)) := by
    calc
      _ ≤ finiteMean (tupleWeight weight) (fun outcome => ∑ changed,
          secondMoment * if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then 1 else 0) := by
        unfold finiteMean
        apply Finset.sum_le_sum
        intro outcome _
        apply mul_le_mul_of_nonneg_left _ (tupleWeight_nonnegative weight weightNonnegative outcome)
        apply Finset.sum_le_sum
        intro changed _
        exact mul_le_mul_of_nonneg_right (secondMomentBound changed) (by split_ifs <;> norm_num)
      _ = _ := by
        simp only [← Finset.mul_sum, indicatorSum, finiteMean]
        simp only [mul_left_comm, Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

end IGSIII.Chemical

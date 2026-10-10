import IGSIII.Chemical.GeodesicSensitivity
import IGSIII.Probability.FiniteResampling
import IGSIII.Probability.ResamplingSymmetry

/-! Finite product variance control for the actual shortest-path functional.
This is the resampling input for conditional variance decay on the innovation tree. -/

set_option autoImplicit false

namespace IGSIII.Chemical

open IGSIII.Probability PathFamily
open scoped BigOperators

variable {Outcome : Type*} [Fintype Outcome] {count : ℕ}

def sampledEdgeCost (localCost : Fin count → Outcome → ℝ)
    (outcome : Fin count → Outcome) : Fin count → ℝ :=
  fun edge => localCost edge (outcome edge)

omit [Fintype Outcome] in
theorem sampledEdgeCost_update (localCost : Fin count → Outcome → ℝ)
    (outcome : Fin count → Outcome) (changed : Fin count) (replacement : Outcome) :
    sampledEdgeCost localCost (Function.update outcome changed replacement) =
      Function.update (sampledEdgeCost localCost outcome) changed (localCost changed replacement) := by
  funext edge
  by_cases equal : edge = changed <;> simp [sampledEdgeCost, equal]

theorem shortest_variance_le_geodesic_resampling
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    (nonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1) :
    finiteVariance (tupleWeight weight) (fun outcome => family.shortest (sampledEdgeCost localCost outcome)) ≤
      finiteMean (tupleWeight weight) (fun outcome => ∑ changed,
        finiteMean (weight changed) (fun replacement =>
          (localCost changed replacement - localCost changed (outcome changed)) ^ 2 *
            ((if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then (1 : ℝ) else 0) +
              if changed ∈ family.minimizingPath
                (sampledEdgeCost localCost (Function.update outcome changed replacement)) then 1 else 0))) := by
  refine (finite_product_variance_le_resampling count weight nonnegative normalized
    (fun outcome => family.shortest (sampledEdgeCost localCost outcome))).trans ?_
  unfold resamplingEnergy finiteMean
  apply Finset.sum_le_sum
  intro outcome _
  apply mul_le_mul_of_nonneg_left _ (tupleWeight_nonnegative weight nonnegative outcome)
  apply Finset.sum_le_sum
  intro changed _
  apply Finset.sum_le_sum
  intro replacement _
  apply mul_le_mul_of_nonneg_left _ (nonnegative changed replacement)
  dsimp only
  rw [sampledEdgeCost_update]
  calc
    (family.shortest (sampledEdgeCost localCost outcome) -
        family.shortest (Function.update (sampledEdgeCost localCost outcome) changed (localCost changed replacement))) ^ 2 =
        (family.shortest (Function.update (sampledEdgeCost localCost outcome) changed (localCost changed replacement)) -
          family.shortest (sampledEdgeCost localCost outcome)) ^ 2 := by ring
    _ ≤ _ := family.shortest_update_sq_le_geodesic_indicators
      (sampledEdgeCost localCost outcome) changed (localCost changed replacement)

noncomputable def geodesicResamplingCost (family : PathFamily (Fin count))
    (localCost : Fin count → Outcome → ℝ) (changed : Fin count)
    (outcome : Fin count → Outcome) (replacement : Outcome) : ℝ :=
  (localCost changed replacement - localCost changed (outcome changed)) ^ 2 *
    if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then 1 else 0

theorem geodesic_resampling_exchange
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    (changed : Fin count) :
    finiteMean (tupleWeight weight) (fun outcome => finiteMean (weight changed)
      (fun replacement => geodesicResamplingCost family localCost changed outcome replacement)) =
      finiteMean (tupleWeight weight) (fun outcome => finiteMean (weight changed)
        (fun replacement => geodesicResamplingCost family localCost changed
          (Function.update outcome changed replacement) (outcome changed))) := by
  have exchange := finiteMean_resampling_exchange weight changed
    (fun pair => geodesicResamplingCost family localCost changed pair.1 pair.2)
  change finiteMean (fun pair : (Fin count → Outcome) × Outcome =>
    tupleWeight weight pair.1 * weight changed pair.2)
      (fun pair => geodesicResamplingCost family localCost changed pair.1 pair.2) =
    finiteMean (fun pair : (Fin count → Outcome) × Outcome =>
      tupleWeight weight pair.1 * weight changed pair.2)
      (fun pair => geodesicResamplingCost family localCost changed
        (Function.update pair.1 changed pair.2) (pair.1 changed)) at exchange
  rw [finiteMean_product (tupleWeight weight) (weight changed)
    (geodesicResamplingCost family localCost changed)] at exchange
  rw [finiteMean_product (tupleWeight weight) (weight changed)
    (fun outcome replacement => geodesicResamplingCost family localCost changed
      (Function.update outcome changed replacement) (outcome changed))] at exchange
  exact exchange

theorem shortest_variance_le_twice_old_geodesic_resampling
    (family : PathFamily (Fin count)) (weight localCost : Fin count → Outcome → ℝ)
    (nonnegative : ∀ edge outcome, 0 ≤ weight edge outcome)
    (normalized : ∀ edge, ∑ outcome, weight edge outcome = 1) :
    finiteVariance (tupleWeight weight) (fun outcome => family.shortest (sampledEdgeCost localCost outcome)) ≤
      2 * finiteMean (tupleWeight weight) (fun outcome => ∑ changed,
        finiteMean (weight changed) (geodesicResamplingCost family localCost changed outcome)) := by
  have coordinateEquality (changed : Fin count) :
      finiteMean (tupleWeight weight) (fun outcome => finiteMean (weight changed) (fun replacement =>
        (localCost changed replacement - localCost changed (outcome changed)) ^ 2 *
          ((if changed ∈ family.minimizingPath (sampledEdgeCost localCost outcome) then (1 : ℝ) else 0) +
            if changed ∈ family.minimizingPath
              (sampledEdgeCost localCost (Function.update outcome changed replacement)) then 1 else 0))) =
        2 * finiteMean (tupleWeight weight) (fun outcome =>
          finiteMean (weight changed) (geodesicResamplingCost family localCost changed outcome)) := by
    have updated (outcome : Fin count → Outcome) (replacement : Outcome) :
        (localCost changed replacement - localCost changed (outcome changed)) ^ 2 *
          (if changed ∈ family.minimizingPath
            (sampledEdgeCost localCost (Function.update outcome changed replacement)) then (1 : ℝ) else 0) =
        geodesicResamplingCost family localCost changed
          (Function.update outcome changed replacement) (outcome changed) := by
      simp only [geodesicResamplingCost, Function.update_self]
      ring
    simp_rw [mul_add, finiteMean_add, updated]
    rw [← geodesic_resampling_exchange family weight localCost changed]
    change finiteMean (tupleWeight weight)
        (fun outcome => finiteMean (weight changed) (geodesicResamplingCost family localCost changed outcome)) +
      finiteMean (tupleWeight weight)
        (fun outcome => finiteMean (weight changed) (geodesicResamplingCost family localCost changed outcome)) = _
    ring
  have meanSum (response : Fin count → (Fin count → Outcome) → ℝ) :
      finiteMean (tupleWeight weight) (fun outcome => ∑ changed, response changed outcome) =
        ∑ changed, finiteMean (tupleWeight weight) (response changed) := by
    unfold finiteMean
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  refine (shortest_variance_le_geodesic_resampling family weight localCost nonnegative normalized).trans_eq ?_
  rw [meanSum]
  simp_rw [coordinateEquality]
  rw [← Finset.mul_sum, ← meanSum]

end IGSIII.Chemical

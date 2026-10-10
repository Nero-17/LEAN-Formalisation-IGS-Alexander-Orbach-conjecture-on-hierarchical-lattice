import Universality.Percolation.MassDistributionSmoothing
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace Universality

open MeasureTheory
open scoped ENNReal BigOperators

/-- For finitely many independent nonnegative variables, the sum vanishes
exactly when every coordinate vanishes, almost surely. -/
theorem independentSumLaw_zero {Index : Type*} [Fintype Index]
    (law : Index → Measure ℝ) [∀ index, IsProbabilityMeasure (law index)]
    (nonnegative : ∀ index, ∀ᵐ value ∂law index, 0 ≤ value) :
    independentSumLaw law {0} = ∏ index, law index {0} := by
  classical
  rw [independentSumLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have coordinates_nonnegative : ∀ᵐ value ∂Measure.pi law, ∀ index, 0 ≤ value index :=
    Measure.ae_le_pi nonnegative
  calc
    _ = Measure.pi law (Set.univ.pi (fun _ => ({0} : Set ℝ))) := by
      apply measure_congr
      filter_upwards [coordinates_nonnegative] with value lower
      apply propext
      change (∑ index, value index) = 0 ↔ ∀ index, index ∈ (Set.univ : Set Index) → value index = 0
      simpa using (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun index _ => lower index))
    _ = _ := Measure.pi_pi _ _

namespace FiniteNetwork

theorem childMassLaw_nonnegative {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ)
    (nonnegative : ∀ state, ∀ᵐ value ∂law state, 0 ≤ value)
    (state : LiveState) (coarse : Configuration edges) (edge : Fin edges) :
    ∀ᵐ value ∂network.childMassLaw law state coarse edge, 0 ≤ value := by
  unfold childMassLaw
  cases network.childState state coarse edge with
  | none => simp
  | some child => exact nonnegative child

/-- The independent offspring-sum law has the exact product zero atom. -/
theorem offspringMassLaw_zero {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (nonnegative : ∀ state, ∀ᵐ value ∂law state, 0 ≤ value)
    (radius : ℝ) (radius_ne_zero : radius ≠ 0)
    (state : LiveState) (coarse : Configuration edges) :
    network.offspringMassLaw law radius state coarse {0} =
      ∏ edge, network.childMassLaw law state coarse edge {0} := by
  rw [offspringMassLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have preimage : (fun value : ℝ => radius⁻¹ * value) ⁻¹' {0} = {0} := by
    ext value
    simp [radius_ne_zero]
  rw [preimage]
  exact independentSumLaw_zero _ (network.childMassLaw_nonnegative law nonnegative state coarse)

/-- Two distinct connected children are sufficient to bound a branch's zero
atom by the square of the connected zero atom. -/
theorem offspringMassLaw_zero_le_square {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (nonnegative : ∀ state, ∀ᵐ value ∂law state, 0 ≤ value)
    (radius : ℝ) (radius_ne_zero : radius ≠ 0)
    (state : LiveState) (coarse : Configuration edges)
    (first second : Fin edges) (distinct : first ≠ second)
    (first_connected : network.childState state coarse first = some .connected)
    (second_connected : network.childState state coarse second = some .connected) :
    network.offspringMassLaw law radius state coarse {0} ≤ (law .connected {0}) ^ 2 := by
  classical
  rw [network.offspringMassLaw_zero law nonnegative radius radius_ne_zero state coarse]
  calc
    _ ≤ ∏ edge, if edge ∈ ({first, second} : Finset (Fin edges)) then law .connected {0} else 1 := by
      apply Finset.prod_le_prod (fun _ _ => bot_le)
      intro edge _
      by_cases selected : edge ∈ ({first, second} : Finset (Fin edges))
      · rw [if_pos selected]
        simp only [Finset.mem_insert, Finset.mem_singleton] at selected
        rcases selected with rfl | rfl
        · simp [childMassLaw, first_connected]
        · simp [childMassLaw, second_connected]
      · rw [if_neg selected]
        exact prob_le_one
    _ = _ := by
      rw [Finset.prod_ite_mem_eq]
      simp [distinct, pow_two]

end FiniteNetwork
end Universality

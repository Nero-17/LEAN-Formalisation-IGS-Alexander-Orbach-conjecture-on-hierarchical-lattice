import IGSIII34.Percolation.ConnectedResistance
import IGSIII34.Resistance.CurrentMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators

theorem electricalCell_resampling_positivePart_sq_le
    {vertices edges : ℕ} (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : rule.crosses configuration = true)
    (resistance : Fin edges → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (edge : Fin edges) (replacement : ℝ) (replacementNonnegative : 0 ≤ replacement) :
    max (electricalCell rule configuration (Function.update resistance edge replacement) -
      electricalCell rule configuration resistance) 0 ^ 2 ≤
        if opened : configuration edge = true then
          replacement^2 * (network rule configuration).minimizingCurrent (connected_of_crosses rule configuration crosses)
            (fun edge => resistance edge.val) (fun edge => positive edge.val) ⟨edge, opened⟩ ^ 4 else 0 := by
  by_cases opened : configuration edge = true
  · rw [dif_pos opened]
    have updated : (fun index : {index : Fin edges // configuration index = true} =>
        Function.update resistance edge replacement index.val) =
        Function.update (fun index : {index : Fin edges // configuration index = true} => resistance index.val)
          ⟨edge, opened⟩ replacement := by
      funext index
      by_cases same : index.val = edge
      · have equality : index = ⟨edge, opened⟩ := Subtype.ext same
        subst index
        simp
      · have unequal : index ≠ ⟨edge, opened⟩ := fun equality => same (congrArg Subtype.val equality)
        simp only [Function.update_of_ne same, Function.update_of_ne unequal]
    unfold electricalCell
    rw [updated]
    exact (network rule configuration).resistance_resampling_positivePart_sq_le
      (connected_of_crosses rule configuration crosses) _ (fun edge => positive edge.val)
      ⟨edge, opened⟩ replacement replacementNonnegative
  · rw [dif_neg opened]
    have unchanged : electricalCell rule configuration (Function.update resistance edge replacement) =
        electricalCell rule configuration resistance := by
      apply electricalCell_congr_open
      intro index isOpen
      have unequal : index ≠ edge := fun same => opened (same ▸ isOpen)
      exact Function.update_of_ne unequal _ _
    rw [unchanged, sub_self, max_self, zero_pow (by norm_num)]

theorem finite_electricalCell_variance_bound
    {vertices edges : ℕ} {State : Type*} [Fintype State]
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : rule.crosses configuration = true)
    (weight : State → ℝ) (nonnegative : ∀ state, 0 ≤ weight state)
    (normalized : ∑ state, weight state = 1)
    (resistance : State → ℝ) (positive : ∀ state, 0 < resistance state) :
    finiteVariance (tupleWeight (fun _ : Fin edges => weight))
      (fun input : Fin edges → State => electricalCell rule configuration (fun edge => resistance (input edge))) ≤
      2 * finiteMean weight (fun state => resistance state^2) *
        finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
          ∑ edge : {edge : Fin edges // configuration edge = true},
            (network rule configuration).minimizingCurrent (connected_of_crosses rule configuration crosses)
              (fun edge => resistance (input edge.val)) (fun edge => positive (input edge.val)) edge^4) := by
  apply (finite_product_variance_le_positive_resampling edges (fun _ => weight)
    (fun _ => nonnegative) (fun _ => normalized) _).trans
  have energyBound : positiveResamplingEnergy (fun _ : Fin edges => weight)
      (fun input => electricalCell rule configuration (fun edge => resistance (input edge))) ≤
      finiteMean weight (fun state => resistance state^2) *
        finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
          ∑ edge : {edge : Fin edges // configuration edge = true},
            (network rule configuration).minimizingCurrent (connected_of_crosses rule configuration crosses)
              (fun edge => resistance (input edge.val)) (fun edge => positive (input edge.val)) edge^4) := by
    unfold positiveResamplingEnergy
    calc
      _ ≤ finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
          ∑ edge, if opened : configuration edge = true then
            finiteMean weight (fun state => resistance state^2) *
              (network rule configuration).minimizingCurrent (connected_of_crosses rule configuration crosses)
                (fun edge => resistance (input edge.val)) (fun edge => positive (input edge.val)) ⟨edge, opened⟩^4 else 0) := by
        apply finiteMean_mono _ (tupleWeight_nonnegative _ (fun _ => nonnegative))
        intro input
        apply Finset.sum_le_sum
        intro edge _
        by_cases opened : configuration edge = true
        · rw [dif_pos opened, ← finiteMean_mul_const]
          apply finiteMean_mono _ nonnegative
          intro replacement
          have updated : (fun index => resistance (Function.update input edge replacement index)) =
              Function.update (fun index => resistance (input index)) edge (resistance replacement) := by
            funext index
            by_cases same : index=edge <;> simp [same]
          dsimp only
          rw [updated]
          simpa only [dif_pos opened] using electricalCell_resampling_positivePart_sq_le rule configuration crosses
            (fun index => resistance (input index)) (fun index => positive (input index)) edge
            (resistance replacement) (positive replacement).le
        · rw [dif_neg opened]
          have allZero : ∀ replacement,
              max (electricalCell rule configuration (fun index => resistance (Function.update input edge replacement index)) -
                electricalCell rule configuration (fun index => resistance (input index))) 0^2 ≤ 0 := by
            intro replacement
            have updated : (fun index => resistance (Function.update input edge replacement index)) =
                Function.update (fun index => resistance (input index)) edge (resistance replacement) := by
              funext index
              by_cases same : index=edge <;> simp [same]
            rw [updated]
            simpa only [dif_neg opened] using electricalCell_resampling_positivePart_sq_le rule configuration crosses
              (fun index => resistance (input index)) (fun index => positive (input index)) edge
              (resistance replacement) (positive replacement).le
          have bound := finiteMean_mono weight nonnegative allZero
          simpa only [finiteMean, mul_zero, Finset.sum_const_zero] using bound
      _ = _ := by
        calc
          _ = finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
              ∑ edge : {edge : Fin edges // configuration edge = true},
                finiteMean weight (fun state => resistance state^2) *
                  (network rule configuration).minimizingCurrent (connected_of_crosses rule configuration crosses)
                    (fun edge => resistance (input edge.val)) (fun edge => positive (input edge.val)) edge^4) := by
            congr 1
            funext input
            rw [Finset.sum_dite]
            simp only [Finset.sum_const_zero, add_zero]
            exact (Equiv.subtypeEquivRight (fun edge : Fin edges => by simp)).sum_comp
              (fun edge : {edge : Fin edges // configuration edge = true} =>
                finiteMean weight (fun state => resistance state^2) *
                  (network rule configuration).minimizingCurrent (connected_of_crosses rule configuration crosses)
                    (fun edge => resistance (input edge.val)) (fun edge => positive (input edge.val)) edge^4)
          _ = _ := by
            simp only [← Finset.mul_sum]
            exact finiteMean_const_mul _ _ _
  exact (mul_le_mul_of_nonneg_left energyBound (by norm_num)).trans_eq (by ring)

theorem finite_electricalCell_current_fourth_moment_bound
    {vertices edges : ℕ} {State : Type*} [Fintype State]
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : rule.crosses configuration = true)
    (weight : State → ℝ) (nonnegative : ∀ state, 0 ≤ weight state)
    (normalized : ∑ state, weight state = 1)
    (resistance : State → ℝ) (positive : ∀ state, 0 < resistance state)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (inverseMoment : ℝ)
    (inverseBound : finiteMean weight (fun state => (resistance state)⁻¹^power) ≤ inverseMoment) :
    finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
      ∑ edge : {edge : Fin edges // configuration edge = true},
        (network rule configuration).minimizingCurrent (connected_of_crosses rule configuration crosses)
          (fun edge => resistance (input edge.val)) (fun edge => positive (input edge.val)) edge^4) ≤
      (finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
        electricalCell rule configuration (fun edge => resistance (input edge))^2))^(1/(2 : ℝ)) *
          ((edges : ℝ)*inverseMoment)^(1/power) := by
  have inverseSumNonnegative : 0 ≤ finiteMean (tupleWeight (fun _ : Fin edges => weight))
      (fun input : Fin edges → State => ∑ edge : {edge : Fin edges // configuration edge = true},
        (resistance (input edge.val))⁻¹^power) := by
    unfold finiteMean
    exact Finset.sum_nonneg (fun input _ => mul_nonneg
      (tupleWeight_nonnegative _ (fun _ => nonnegative) input)
      (Finset.sum_nonneg (fun edge _ => Real.rpow_nonneg (inv_nonneg.mpr (positive (input edge.val)).le) power)))
  have inverseSumBound : finiteMean (tupleWeight (fun _ : Fin edges => weight))
      (fun input : Fin edges → State => ∑ edge : {edge : Fin edges // configuration edge = true},
        (resistance (input edge.val))⁻¹^power) ≤ (edges : ℝ)*inverseMoment := by
    calc
      _ ≤ finiteMean (tupleWeight (fun _ : Fin edges => weight))
          (fun input : Fin edges → State => ∑ edge : Fin edges, (resistance (input edge))⁻¹^power) := by
        apply finiteMean_mono _ (tupleWeight_nonnegative _ (fun _ => nonnegative))
        intro input
        exact sum_open_edges_le_sum configuration _ (fun edge => Real.rpow_nonneg (inv_nonneg.mpr (positive (input edge)).le) power)
      _ = ∑ _edge : Fin edges, finiteMean weight (fun state => (resistance state)⁻¹^power) := by
        exact IGSIII.Chemical.finiteMean_tuple_sum_local (fun _ : Fin edges => weight)
          (fun _ state => (resistance state)⁻¹^power) (fun _ => normalized)
      _ ≤ ∑ _edge : Fin edges, inverseMoment := Finset.sum_le_sum (fun _ _ => inverseBound)
      _ = _ := by simp
  have currentBound := (network rule configuration).finite_current_fourth_moment_le_inverse_envelope
    (connected_of_crosses rule configuration crosses) (tupleWeight (fun _ : Fin edges => weight))
    (tupleWeight_nonnegative _ (fun _ => nonnegative)) (tupleWeight_normalized _ (fun _ => normalized))
    (fun input edge => resistance (input edge.val)) (fun input edge => positive (input edge.val)) powerAtLeastTwo
  apply currentBound.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow inverseSumNonnegative inverseSumBound (by
      have powerPositive := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) powerAtLeastTwo
      positivity))
  apply Real.rpow_nonneg
  unfold finiteMean
  exact Finset.sum_nonneg (fun input _ => mul_nonneg
    (tupleWeight_nonnegative _ (fun _ => nonnegative) input) (sq_nonneg _))

theorem finite_electricalCell_variance_le_product_moments
    {vertices edges : ℕ} {State : Type*} [Fintype State]
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : rule.crosses configuration = true)
    (weight : State → ℝ) (nonnegative : ∀ state, 0 ≤ weight state)
    (normalized : ∑ state, weight state = 1)
    (resistance : State → ℝ) (positive : ∀ state, 0 < resistance state)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (inverseMoment : ℝ)
    (inverseBound : finiteMean weight (fun state => (resistance state)⁻¹^power) ≤ inverseMoment) :
    finiteVariance (tupleWeight (fun _ : Fin edges => weight))
      (fun input : Fin edges → State => electricalCell rule configuration (fun edge => resistance (input edge))) ≤
      2*finiteMean weight (fun state => resistance state^2) *
        (finiteMean (tupleWeight (fun _ : Fin edges => weight)) (fun input : Fin edges → State =>
          electricalCell rule configuration (fun edge => resistance (input edge))^2))^(1/(2 : ℝ)) *
            ((edges : ℝ)*inverseMoment)^(1/power) := by
  have secondMomentNonnegative : 0 ≤ finiteMean weight (fun state => resistance state^2) :=
    Finset.sum_nonneg (fun state _ => mul_nonneg (nonnegative state) (sq_nonneg _))
  apply (finite_electricalCell_variance_bound rule configuration crosses weight nonnegative normalized resistance positive).trans
  exact (mul_le_mul_of_nonneg_left
    (finite_electricalCell_current_fourth_moment_bound rule configuration crosses weight nonnegative normalized resistance positive
      powerAtLeastTwo inverseMoment inverseBound) (mul_nonneg (by norm_num) secondMomentNonnegative)).trans_eq (by ring)

end
end IGSIII34.Percolation

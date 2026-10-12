import IGSIII34.ResistanceLimit.LimitEnergy
import IGSIII34.Forms.CompletionExtension

/-! Half-line projections have positive energy pairing with the original
function. This is derived on actual finite edges and then passed to the
increasing trace-energy limit. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Filter IGSIII34.Forms
open scoped Topology BigOperators

theorem real_negative_part_pairing_completion (first second : ℝ) :
    (min first 0 - min second 0) ^ 2 ≤
      (first - second) * (min first 0 - min second 0) := by
  by_cases firstNonpositive : first ≤ 0 <;> by_cases secondNonpositive : second ≤ 0
  · rw [min_eq_left firstNonpositive, min_eq_left secondNonpositive]; nlinarith
  · rw [min_eq_left firstNonpositive, min_eq_right (le_of_not_ge secondNonpositive)]; nlinarith
  · rw [min_eq_right (le_of_not_ge firstNonpositive), min_eq_left secondNonpositive]; nlinarith
  · rw [min_eq_right (le_of_not_ge firstNonpositive), min_eq_right (le_of_not_ge secondNonpositive)]; simp

theorem real_upper_excess_pairing_completion (first second threshold : ℝ) :
    (max (first - threshold) 0 - max (second - threshold) 0) ^ 2 ≤
      (first - second) * (max (first - threshold) 0 - max (second - threshold) 0) := by
  by_cases firstAbove : 0 ≤ first - threshold <;> by_cases secondAbove : 0 ≤ second - threshold
  · rw [max_eq_left firstAbove, max_eq_left secondAbove]; nlinarith
  · rw [max_eq_left firstAbove, max_eq_right (le_of_not_ge secondAbove)]; nlinarith
  · rw [max_eq_right (le_of_not_ge firstAbove), max_eq_left secondAbove]; nlinarith
  · rw [max_eq_right (le_of_not_ge firstAbove), max_eq_right (le_of_not_ge secondAbove)]; simp

variable {Carrier : Type*} {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
  (conductance : ∀ depth, Edge depth → ℝ)
  (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
  (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))

include monotone in
theorem limitingEnergy_le_pairing_truncation_completion
    (contraction : ℝ → ℝ)
    (contracts : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    (firm : ∀ first second, (contraction first - contraction second)^2 ≤
      (first - second) * (contraction first - contraction second))
    (potential : energyDomain endpoint conductance nonnegative) :
    limitingEnergy endpoint conductance (fun point => contraction (potential.val point)) ≤
      limitingPairing endpoint conductance potential.val (fun point => contraction (potential.val point)) := by
  have contracted := energyDomain_normal_contraction endpoint conductance nonnegative contraction contracts potential.property
  apply le_of_tendsto_of_tendsto
    (traceEnergy_tendsto endpoint conductance nonnegative contracted (monotone _))
    (tracePairing_tendsto endpoint conductance nonnegative monotone potential.property contracted)
  apply Eventually.of_forall
  intro depth
  unfold traceEnergy tracePairing finiteEnergy finitePairing
  apply Finset.sum_le_sum
  intro edge _
  have inequality := mul_le_mul_of_nonneg_left
    (firm (potential.val (endpoint depth edge).1) (potential.val (endpoint depth edge).2)) (nonnegative depth edge)
  simpa only [mul_assoc] using inequality

theorem negative_part_contracts_completion (first second : ℝ) :
    |min first 0 - min second 0| ≤ |first - second| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using
    (LipschitzWith.id.min_const (0 : ℝ)).dist_le_mul first second

theorem upper_excess_contracts_completion (first second threshold : ℝ) :
    |max (first-threshold) 0 - max (second-threshold) 0| ≤ |first-second| := by
  have inequality := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul (first-threshold) (second-threshold)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right, id_eq] using inequality

include monotone in
theorem limitingEnergy_negative_part_le_pairing_completion
    (potential : energyDomain endpoint conductance nonnegative) :
    limitingEnergy endpoint conductance (fun point => min (potential.val point) 0) ≤
      limitingPairing endpoint conductance potential.val (fun point => min (potential.val point) 0) :=
  limitingEnergy_le_pairing_truncation_completion endpoint conductance nonnegative monotone
    (fun value => min value 0) negative_part_contracts_completion
    real_negative_part_pairing_completion potential

include monotone in
theorem limitingEnergy_upper_excess_le_pairing_completion
    (potential : energyDomain endpoint conductance nonnegative) (threshold : ℝ) :
    limitingEnergy endpoint conductance (fun point => max (potential.val point-threshold) 0) ≤
      limitingPairing endpoint conductance potential.val (fun point => max (potential.val point-threshold) 0) :=
  limitingEnergy_le_pairing_truncation_completion endpoint conductance nonnegative monotone
    (fun value => max (value-threshold) 0) (fun first second => upper_excess_contracts_completion first second threshold)
    (fun first second => real_upper_excess_pairing_completion first second threshold) potential

variable [MetricSpace Carrier]
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first-potential second)^2 ≤ dist first second * limitingEnergy endpoint conductance potential)

include resistanceBound in
theorem completionExtension_contraction_completion
    (contraction : ℝ → ℝ) (contractionContinuous : Continuous contraction)
    (contracts : ∀ first second, |contraction first-contraction second| ≤ |first-second|)
    (potential : energyDomain endpoint conductance nonnegative) (point : UniformSpace.Completion Carrier) :
    completionExtension endpoint conductance nonnegative
      ⟨fun vertex => contraction (potential.val vertex),
        energyDomain_normal_contraction endpoint conductance nonnegative contraction contracts potential.property⟩ point =
    contraction (completionExtension endpoint conductance nonnegative potential point) := by
  have equality := (UniformSpace.Completion.denseRange_coe (α := Carrier)).equalizer
    (completionExtension endpoint conductance nonnegative ⟨_, energyDomain_normal_contraction endpoint conductance nonnegative
      contraction contracts potential.property⟩).continuous
    (contractionContinuous.comp (completionExtension endpoint conductance nonnegative potential).continuous)
    (by
      funext vertex
      change completionExtension endpoint conductance nonnegative ⟨_, _⟩ (vertex : UniformSpace.Completion Carrier) =
        contraction (completionExtension endpoint conductance nonnegative potential (vertex : UniformSpace.Completion Carrier))
      rw [completionExtension_coe endpoint conductance nonnegative resistanceBound,
        completionExtension_coe endpoint conductance nonnegative resistanceBound])
  exact congrFun equality point

end
end IGSIII34.ResistanceLimit

import IGSIII4.SpectralDensity.ActualCrossing20261012
import IGSIII4.SpectralDensity.BernoulliCircuit20261012

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork
open scoped BigOperators

abbrev CircuitConfiguration (blocks paths interior : ℕ) :=
  Configuration 4 × (Fin blocks → Fin paths → Configuration (interior + 2))

def configurationEquiv (blocks paths interior : ℕ) :
    Configuration (Fintype.card (Edge blocks paths interior)) ≃ CircuitConfiguration blocks paths interior where
  toFun configuration :=
    (fun edge => configuration (Fintype.equivFin _ (.inl edge)),
      fun block path edge => configuration (Fintype.equivFin _ (.inr (block, path, edge))))
  invFun configuration edge :=
    match (Fintype.equivFin (Edge blocks paths interior)).symm edge with
    | .inl outer => configuration.1 outer
    | .inr (block, path, inner) => configuration.2 block path inner
  left_inv configuration := by
    funext edge
    have identity := congrArg configuration ((Fintype.equivFin (Edge blocks paths interior)).apply_symm_apply edge)
    cases equal : (Fintype.equivFin (Edge blocks paths interior)).symm edge with
    | inl outer => simpa only [equal] using identity
    | inr triple => rcases triple with ⟨block, path, inner⟩; simpa only [equal] using identity
  right_inv configuration := by
    rcases configuration with ⟨outer, inner⟩
    apply Prod.ext
    · funext edge; simp
    · funext block path edge; simp

theorem configuration_weight (blocks paths interior : ℕ) (probability : ℝ)
    (configuration : Configuration (Fintype.card (Edge blocks paths interior))) :
    bernoulliWeight probability configuration =
      bernoulliWeight probability ((configurationEquiv blocks paths interior) configuration).1 *
        chainWeight blocks paths (interior + 2) probability
          ((configurationEquiv blocks paths interior) configuration).2 := by
  unfold bernoulliWeight chainWeight blockWeight
  calc
    _ = ∏ edge : Edge blocks paths interior,
        if configuration (Fintype.equivFin _ edge) then probability else 1 - probability :=
      ((Fintype.equivFin (Edge blocks paths interior)).prod_comp _).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_prod_type, configurationEquiv, Equiv.coe_fn_mk, bernoulliWeight]

/-- The actual finite Bernoulli expectation reindexes into independent outer and block variables. -/
theorem configuration_sum_transfer (blocks paths interior : ℕ) (probability : ℝ)
    (response : CircuitConfiguration blocks paths interior → ℝ) :
    (∑ configuration : Configuration (Fintype.card (Edge blocks paths interior)),
      bernoulliWeight probability configuration * response ((configurationEquiv blocks paths interior) configuration)) =
    ∑ inner : Fin blocks → Fin paths → Configuration (interior + 2),
      chainWeight blocks paths (interior + 2) probability inner *
        expectation probability (fun outer => response (outer, inner)) := by
  simp_rw [configuration_weight]
  rw [(configurationEquiv blocks paths interior).sum_comp (fun configuration =>
    bernoulliWeight probability configuration.1 * chainWeight blocks paths (interior + 2) probability configuration.2 *
      response configuration)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inner _
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outer _
  ring

theorem configuration_crossing (blocks paths interior : ℕ)
    (configuration : Configuration (Fintype.card (Edge blocks paths interior))) :
    (network blocks paths interior).crosses configuration = true ↔
    outerCrossing (chainCrossing blocks paths (interior + 2)
      ((configurationEquiv blocks paths interior) configuration).2)
      ((configurationEquiv blocks paths interior) configuration).1 := by
  rw [network_crosses_iff_circuit]
  rfl

theorem reliability_formula (blocks paths interior : ℕ) (probability : ℝ) :
    (network blocks paths interior).reliability probability =
      probability ^ 2 + (1 - probability ^ 2) * probability ^ 2 *
        (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks := by
  rw [← full_circuit_crossing_probability blocks paths (interior + 2) probability]
  unfold reliability
  calc
    _ = ∑ configuration : Configuration (Fintype.card (Edge blocks paths interior)),
        (if outerCrossing
          (chainCrossing blocks paths (interior + 2) ((configurationEquiv blocks paths interior) configuration).2)
          ((configurationEquiv blocks paths interior) configuration).1 then
          bernoulliWeight probability ((configurationEquiv blocks paths interior) configuration).1 *
            chainWeight blocks paths (interior + 2) probability
              ((configurationEquiv blocks paths interior) configuration).2 else 0) := by
      apply Finset.sum_congr rfl
      intro configuration _
      rw [configuration_weight]
      simp only [configuration_crossing]
    _ = ∑ configuration : CircuitConfiguration blocks paths interior,
        (if outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 then
          bernoulliWeight probability configuration.1 *
            chainWeight blocks paths (interior + 2) probability configuration.2 else 0) :=
      (configurationEquiv blocks paths interior).sum_comp (fun configuration =>
        if outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 then
          bernoulliWeight probability configuration.1 * chainWeight blocks paths (interior + 2) probability configuration.2
        else 0)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro inner _
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outer _
      by_cases crossing : outerCrossing (chainCrossing blocks paths (interior + 2) inner) outer
      · simp [crossing, mul_comm]
      · simp [crossing]

theorem actual_critical_equation (blocks paths interior : ℕ) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : (network blocks paths interior).reliability probability = probability) :
    (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks =
      1 / (probability * (1 + probability)) := by
  rw [reliability_formula] at fixedPoint
  exact critical_chain_probability probability _ positive belowOne fixedPoint

theorem appendixRule_reliability (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length)
    (probability : ℝ) :
    (appendixRule base length).network.reliability probability =
      probability ^ 2 + (1 - probability ^ 2) * probability ^ 2 *
        (1 - (1 - probability ^ length) ^ ⌈(length : ℝ) * (4 / 3 : ℝ) ^ length⌉₊) ^ ⌈base ^ length⌉₊ := by
  change (network _ _ _).reliability probability = _
  rw [reliability_formula, Nat.sub_add_cancel lengthLarge]

end
end IGSIII4.SpectralDensity.ActualFamily

import IGSIII4.SpectralDensity.ActualProbability20261012
import IGSIII4.SpectralDensity.ActualMassBridge20261012

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem outer_long_probability (probability : ℝ) (chainEvent : Prop) :
    expectation probability (fun outer : Configuration 4 =>
      if outer 2 = true ∧ outer 3 = true ∧ chainEvent then 1 else 0) =
      probability ^ 2 * (if chainEvent then 1 else 0) := by
  have consFourOne (head : Bool) (tail : Configuration 3) : (Fin.cons head tail : Configuration 4) (1 : Fin 4) = tail 0 := by
    change (Fin.cons head tail : Configuration 4) (Fin.succ (0 : Fin 3)) = tail 0
    rfl
  have consFourTwo (head : Bool) (tail : Configuration 3) : (Fin.cons head tail : Configuration 4) (2 : Fin 4) = tail 1 := by
    change (Fin.cons head tail : Configuration 4) (Fin.succ (1 : Fin 3)) = tail 1
    rfl
  have consFourThree (head : Bool) (tail : Configuration 3) : (Fin.cons head tail : Configuration 4) (3 : Fin 4) = tail 2 := by
    change (Fin.cons head tail : Configuration 4) (Fin.succ (2 : Fin 3)) = tail 2
    rfl
  have consThreeOne (head : Bool) (tail : Configuration 2) : (Fin.cons head tail : Configuration 3) (1 : Fin 3) = tail 0 := by
    change (Fin.cons head tail : Configuration 3) (Fin.succ (0 : Fin 2)) = tail 0
    rfl
  have consThreeTwo (head : Bool) (tail : Configuration 2) : (Fin.cons head tail : Configuration 3) (2 : Fin 3) = tail 1 := by
    change (Fin.cons head tail : Configuration 3) (Fin.succ (1 : Fin 2)) = tail 1
    rfl
  have consTwoOne (head : Bool) (tail : Configuration 1) : (Fin.cons head tail : Configuration 2) (1 : Fin 2) = tail 0 := by
    change (Fin.cons head tail : Configuration 2) (Fin.succ (0 : Fin 1)) = tail 0
    rfl
  by_cases chainEvent <;>
    simp [expectation_cons, expectation_const, Fin.cons_zero,
      consFourOne, consFourTwo, consFourThree, consThreeOne, consThreeTwo, consTwoOne, *] <;> ring

theorem longEvent_probability (blocks paths interior : ℕ) (probability : ℝ) :
    expectation probability (fun configuration => if LongEvent blocks paths interior configuration then 1 else 0) =
      probability ^ 2 * (1 - (1 - probability ^ (interior + 2)) ^ paths) ^ blocks := by
  have eventRewrite (configuration : Configuration (Fintype.card (Edge blocks paths interior))) :
      LongEvent blocks paths interior configuration ↔
        ((configurationEquiv blocks paths interior) configuration).1 2 = true ∧
          ((configurationEquiv blocks paths interior) configuration).1 3 = true ∧
          chainCrossing blocks paths (interior + 2) ((configurationEquiv blocks paths interior) configuration).2 := by
    rfl
  simp_rw [eventRewrite]
  change (∑ configuration : Configuration (Fintype.card (Edge blocks paths interior)),
    bernoulliWeight probability configuration *
      (if ((configurationEquiv blocks paths interior) configuration).1 2 = true ∧
          ((configurationEquiv blocks paths interior) configuration).1 3 = true ∧
          chainCrossing blocks paths (interior + 2) ((configurationEquiv blocks paths interior) configuration).2
        then 1 else 0)) = _
  rw [configuration_sum_transfer blocks paths interior probability (fun configuration =>
    if configuration.1 2 = true ∧ configuration.1 3 = true ∧
        chainCrossing blocks paths (interior + 2) configuration.2 then 1 else 0)]
  simp_rw [outer_long_probability]
  calc
    _ = probability ^ 2 * ∑ inner : Fin blocks → Fin paths → Configuration (interior + 2),
        if chainCrossing blocks paths (interior + 2) inner then
          chainWeight blocks paths (interior + 2) probability inner else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro inner _
      split_ifs <;> ring
    _ = _ := by rw [chain_crossing_probability]

theorem critical_longEvent_probability (blocks paths interior : ℕ) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability) :
    expectation probability (fun configuration => if LongEvent blocks paths interior configuration then 1 else 0) =
      probability / (1 + probability) := by
  rw [longEvent_probability, actual_critical_equation blocks paths interior probability positive belowOne critical]
  field_simp [positive.ne', (show 1 + probability ≠ 0 by linarith)]

theorem actual_connected_mass_lower (blocks paths interior : ℕ) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability) :
    ((blocks * paths : ℕ) : ℝ) * (probability / (1 + probability)) ≤
      (network blocks paths interior).massMatrix probability .connected .connected := by
  have lower := actual_connected_mass_first_edges_lower blocks paths interior probability positive belowOne critical
  rwa [critical_longEvent_probability blocks paths interior probability positive belowOne critical] at lower

end
end IGSIII4.SpectralDensity.ActualFamily

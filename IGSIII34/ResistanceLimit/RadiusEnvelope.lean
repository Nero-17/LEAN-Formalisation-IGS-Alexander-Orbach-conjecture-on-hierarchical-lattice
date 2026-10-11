import IGSIII34.ResistanceLimit.RadiusRecursion

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

theorem unit_terminalResistanceRadius_le_edges {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges) :
    terminalResistanceRadius (IGSIII34.Percolation.network network configuration) (fun _ => 1) ≤ (edges : ℝ) := by
  have cardBound : (Fintype.card {edge : Fin edges // configuration edge = true} : ℝ) ≤ (edges : ℝ) := by
    exact_mod_cast (show Fintype.card {edge : Fin edges // configuration edge = true} ≤ edges by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun edge : Fin edges => configuration edge = true))
  have bound (first last : Fin vertices) :
      pairResistance (IGSIII34.Percolation.network network configuration) (fun _ => 1) first last ≤ (edges : ℝ) := by
    by_cases reachable : (IGSIII34.Percolation.network network configuration).graph.Reachable first last
    · have comparison := pairResistance_le_sum (IGSIII34.Percolation.network network configuration)
        (fun _ => 1) (fun _ => zero_lt_one) first last reachable
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at comparison
      exact comparison.trans cardBound
    · rw [pairResistance_eq_zero_of_unreachable _ _ reachable]
      positivity
  apply (Finset.sup'_le_iff _ _).mpr
  intro vertex _
  exact max_le (bound network.source vertex) (bound network.target vertex)

theorem marked_electrical_radius_uniform_bound (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (scale eta coefficient amplitude : ℝ) (start : ℕ)
    (amplitudeNonnegative : 0 ≤ amplitude) (scaleGreaterThanOne : 1 < scale) (etaPositive : 0 < eta)
    (growthAtLeastOne : 1 ≤ scale * eta) (coefficientLarge : (rule.edges : ℝ) ≤ coefficient)
    (coefficientContracts : eta * (coefficient + rule.edges * amplitude) ≤ coefficient)
    (terminalEnvelope : ∀ address opened depth, start ≤ address.length →
      unitConfigurationResistance (rule.generation depth).network (markedGenerationConfiguration rule marks depth address opened) ≤
        amplitude * scale ^ (depth + 1) * (scale * eta) ^ address.length) :
    ∀ depth address opened, start ≤ address.length →
      markedElectricalRadius rule marks depth address opened ≤
        coefficient * scale ^ (depth + 1) * (scale * eta) ^ address.length := by
  have scalePositive := zero_lt_one.trans scaleGreaterThanOne
  have growthPositive := mul_pos scalePositive etaPositive
  have coefficientNonnegative : 0 ≤ coefficient := (Nat.cast_nonneg rule.edges).trans coefficientLarge
  intro depth
  induction depth with
  | zero =>
    intro address opened _
    have seed : markedElectricalRadius rule marks 0 address opened ≤ rule.edges :=
      unit_terminalResistanceRadius_le_edges rule.network (marks (address, opened))
    calc
      _ ≤ coefficient := seed.trans coefficientLarge
      _ ≤ coefficient * scale := by nlinarith
      _ ≤ coefficient * scale ^ (0 + 1) * (scale * eta) ^ address.length := by
        simpa using le_mul_of_one_le_right (mul_nonneg coefficientNonnegative scalePositive.le)
          (one_le_pow₀ growthAtLeastOne)
  | succ depth inductionHypothesis =>
    intro address opened beyond
    have childBeyond (edge : Fin rule.edges) : start ≤ (address ++ [edge]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    have actualRecursion := markedElectricalRadius_succ_le rule marks depth address opened
      (coefficient * scale ^ (depth + 1) * (scale * eta) ^ (address.length + 1))
      (amplitude * scale ^ (depth + 1) * (scale * eta) ^ (address.length + 1))
      (by positivity) (by positivity)
      (fun edge => by simpa only [List.length_append, List.length_singleton] using
        inductionHypothesis (address ++ [edge]) (marks (address, opened) edge) (childBeyond edge))
      (fun edge => by simpa only [List.length_append, List.length_singleton] using
        terminalEnvelope (address ++ [edge]) (marks (address, opened) edge) depth (childBeyond edge))
    have factorBound : (scale * eta) * (coefficient + rule.edges * amplitude) ≤ coefficient * scale := by
      nlinarith [mul_le_mul_of_nonneg_left coefficientContracts scalePositive.le]
    have productBound := mul_le_mul_of_nonneg_left factorBound
      (mul_nonneg (pow_nonneg scalePositive.le (depth + 1)) (pow_nonneg growthPositive.le address.length))
    calc
      _ ≤ _ := actualRecursion
      _ = scale ^ (depth + 1) * (scale * eta) ^ address.length *
          ((scale * eta) * (coefficient + rule.edges * amplitude)) := by
        rw [pow_succ (scale * eta) address.length]
        ring
      _ ≤ scale ^ (depth + 1) * (scale * eta) ^ address.length * (coefficient * scale) := productBound
      _ = _ := by rw [pow_succ scale (depth + 1)]; ring

end
end IGSIII34.ResistanceLimit

import Universality.Arithmetic.GraphFixedPointPolynomial
import Universality.Graph.CrossingOpenCount
import Universality.Graph.TerminalEdgeConnectivity

namespace Universality.FiniteNetwork
noncomputable section
open Polynomial

variable {vertices edges : ℕ}

theorem integer_configurationPolynomial_eq (configuration : Configuration edges) :
    (∏ edge : Fin edges, if configuration edge then (X : ℤ[X]) else 1 - X) =
      X ^ openCount configuration * (1 - X) ^ (edges - openCount configuration) := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun edge : Fin edges => configuration edge = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hclosed : (Finset.univ.filter fun edge : Fin edges => ¬ configuration edge = true).card =
      edges - openCount configuration := by
    unfold openCount
    omega
  rw [hclosed]
  rfl

theorem integer_configurationPolynomial_coeff_two (configuration : Configuration edges)
    (hsize : 2 ≤ openCount configuration) :
    (∏ edge : Fin edges, if configuration edge then (X : ℤ[X]) else 1 - X).coeff 2 =
      if openCount configuration = 2 then 1 else 0 := by
  rw [integer_configurationPolynomial_eq, coeff_X_pow_mul']
  by_cases hequal : openCount configuration = 2
  · simp [hequal, coeff_zero_eq_eval_zero]
  · have hlarge : ¬ openCount configuration ≤ 2 := by omega
    simp [hequal, hlarge]

theorem integer_eventPolynomial_coeff_two (event : Configuration edges → Bool)
    (hsize : ∀ configuration, event configuration = true → 2 ≤ openCount configuration) :
    (∑ configuration : Configuration edges, if event configuration then
      ∏ edge : Fin edges, if configuration edge then (X : ℤ[X]) else 1 - X else 0).coeff 2 =
      ((Finset.univ.filter fun configuration : Configuration edges =>
        event configuration = true ∧ openCount configuration = 2).card : ℤ) := by
  simp only [finsetSum_coeff]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases hevent : event configuration = true
  · simp only [hevent, ↓reduceIte, true_and]
    exact integer_configurationPolynomial_coeff_two configuration (hsize configuration hevent)
  · simp [hevent]

theorem integerReliabilityPolynomial_coeff_two (network : FiniteNetwork vertices edges)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    network.integerReliabilityPolynomial.coeff 2 = (network.crossingCountBySize 2 : ℤ) := by
  apply integer_eventPolynomial_coeff_two
  intro configuration hcross
  have hbound := network.distance_le_openCount configuration hcross
  omega

theorem closedCount_at_least_two (network : FiniteNetwork vertices edges)
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hcut : ∀ edge, network.crosses (onlyClosed edge) = true)
    (configuration : Configuration edges) (hfailure : network.crosses configuration = false) :
    2 ≤ openCount (fun edge => !(configuration edge)) := by
  let deleted := Finset.univ.filter fun edge : Fin edges => configuration edge = false
  have hdeleted : network.IsTerminalCut deleted := by
    have hequal : (fun edge => decide (edge ∉ deleted)) = configuration := by
      funext edge
      simp only [deleted, Finset.mem_filter, Finset.mem_univ, true_and]
      cases configuration edge <;> simp
    simpa only [IsTerminalCut, hequal] using hfailure
  have hbound := network.terminalEdgeConnectivity_le deleted hdeleted
  have hminimum := (network.terminalEdgeConnectivity_at_least_two_iff hconnected).mpr hcut
  have hcount : deleted.card = openCount (fun edge => !(configuration edge)) := by
    simp [deleted, openCount]
  omega

theorem integerComplementReliabilityPolynomial_sum (network : FiniteNetwork vertices edges) :
    1 - network.integerReliabilityPolynomial.comp (1 - X) =
      ∑ configuration : Configuration edges, if network.crosses configuration = false then
        ∏ edge : Fin edges, if !(configuration edge) then (X : ℤ[X]) else 1 - X else 0 := by
  have hsum : (∑ configuration : Configuration edges,
      ∏ edge : Fin edges, if !(configuration edge) then (X : ℤ[X]) else 1 - X) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin edges) (opened : Bool) =>
      if !opened then (X : ℤ[X]) else 1 - X)]
    simp
  have hcomp : network.integerReliabilityPolynomial.comp (1 - X) =
      ∑ configuration : Configuration edges, if network.crosses configuration then
        ∏ edge : Fin edges, if !(configuration edge) then (X : ℤ[X]) else 1 - X else 0 := by
    simp only [integerReliabilityPolynomial, sum_comp]
    apply Finset.sum_congr rfl
    intro configuration _
    cases hcross : network.crosses configuration
    · simp
    · simp only [↓reduceIte, prod_comp]
      apply Finset.prod_congr rfl
      intro edge _
      cases configuration edge <;> simp
  rw [hcomp]
  nth_rw 1 [← hsum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro configuration _
  cases network.crosses configuration <;> simp

theorem integerComplementReliabilityPolynomial_coeff_two (network : FiniteNetwork vertices edges)
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hcut : ∀ edge, network.crosses (onlyClosed edge) = true) :
    (1 - network.integerReliabilityPolynomial.comp (1 - X)).coeff 2 =
      ((Finset.univ.filter fun configuration : Configuration edges =>
        network.crosses configuration = false ∧
        openCount (fun edge => !(configuration edge)) = 2).card : ℤ) := by
  rw [integerComplementReliabilityPolynomial_sum]
  simp only [finsetSum_coeff]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases hfailure : network.crosses configuration = false
  · simp only [hfailure, ↓reduceIte, true_and]
    exact integer_configurationPolynomial_coeff_two _
      (closedCount_at_least_two network hconnected hcut configuration hfailure)
  · simp [hfailure]
theorem integerFixedPointPolynomial_mod_two_nonconstant_of_parity
    (network : FiniteNetwork vertices edges)
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target)
    (hcut : ∀ edge, network.crosses (onlyClosed edge) = true)
    (hparity : Even (network.crossingCountBySize 2) ∨
      Even ((Finset.univ.filter fun configuration : Configuration edges =>
        network.crosses configuration = false ∧
        openCount (fun edge => !(configuration edge)) = 2).card)) :
    ((network.integerFixedPointPolynomial hconnected).map (Int.castRingHom (ZMod 2))).natDegree ≠ 0 := by
  intro hconstant
  have htwo : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  have hneg (polynomial : (ZMod 2)[X]) : -polynomial = polynomial := by
    apply neg_eq_of_add_eq_zero_left
    rw [← two_mul, htwo, zero_mul]
  have hzero : ((network.integerFixedPointPolynomial hconnected).map
      (Int.castRingHom (ZMod 2))).eval 0 = -1 := by
    rw [eval_zero_map, network.integerFixedPointPolynomial_zero hconnected hscale]
    simp
  have hform := eq_C_of_natDegree_eq_zero hconstant
  have hfixedPoint : (network.integerFixedPointPolynomial hconnected).map
      (Int.castRingHom (ZMod 2)) = 1 := by
    rw [hform, eval_C] at hzero
    rw [hform, hzero]
    simp only [map_neg, map_one, hneg]
  have hfactor := congrArg (Polynomial.map (Int.castRingHom (ZMod 2)))
    (network.integerFixedPointPolynomial_factor hconnected)
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_mul,
    Polynomial.map_one, hfixedPoint, mul_one] at hfactor
  have hreliability : network.integerReliabilityPolynomial.map (Int.castRingHom (ZMod 2)) = X ^ 2 := by
    linear_combination (norm := (ring_nf; simp [htwo])) hfactor
  have hcomplement : (1 - network.integerReliabilityPolynomial.comp (1 - X)).map
      (Int.castRingHom (ZMod 2)) = X ^ 2 := by
    rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_comp,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, hreliability]
    simp only [pow_comp, X_comp]
    ring_nf
    simp [htwo, hneg]
  have hfirst := congrArg (fun polynomial : (ZMod 2)[X] => polynomial.coeff 2) hreliability
  have hsecond := congrArg (fun polynomial : (ZMod 2)[X] => polynomial.coeff 2) hcomplement
  simp only [coeff_map, coeff_X_pow, ↓reduceIte, map_natCast,
    network.integerReliabilityPolynomial_coeff_two hscale] at hfirst
  simp only [coeff_map, coeff_X_pow, ↓reduceIte, map_natCast,
    network.integerComplementReliabilityPolynomial_coeff_two hconnected hcut] at hsecond
  rcases hparity with hparity | hparity
  · have hzero := hparity.natCast_zmod_two
    rw [hzero] at hfirst
    exact zero_ne_one hfirst
  · have hzero := hparity.natCast_zmod_two
    rw [hzero] at hsecond
    exact zero_ne_one hsecond
set_option maxHeartbeats 1600000 in
theorem integerFixedPointPolynomial_mod_prime_nonconstant_of_mod_two
    (network : FiniteNetwork vertices edges)
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target)
    (hcut : ∀ edge, network.crosses (onlyClosed edge) = true)
    (hmodTwo : ((network.integerFixedPointPolynomial hconnected).map
      (Int.castRingHom (ZMod 2))).natDegree ≠ 0)
    (prime : ℕ) (hprime : prime.Prime) :
    ((network.integerFixedPointPolynomial hconnected).map (Int.castRingHom (ZMod prime))).natDegree ≠ 0 := by
  letI : Fact prime.Prime := ⟨hprime⟩
  by_cases hequal : prime = 2
  · subst prime
    exact hmodTwo
  intro hconstant
  have hzero : ((network.integerFixedPointPolynomial hconnected).map
      (Int.castRingHom (ZMod prime))).eval 0 = -1 := by
    rw [eval_zero_map, network.integerFixedPointPolynomial_zero hconnected hscale]
    simp
  have hone : ((network.integerFixedPointPolynomial hconnected).map
      (Int.castRingHom (ZMod prime))).eval 1 = 1 := by
    rw [eval_one_map, network.integerFixedPointPolynomial_one hconnected hcut]
    simp
  have hform := eq_C_of_natDegree_eq_zero hconstant
  rw [hform, eval_C] at hzero hone
  have htwo : (2 : ZMod prime) = 0 := by
    linear_combination hzero - hone
  have hdivides : prime ∣ 2 := (CharP.cast_eq_zero_iff (ZMod prime) prime 2).mp htwo
  exact hequal ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hdivides)

end
end Universality.FiniteNetwork

#print axioms Universality.FiniteNetwork.integerReliabilityPolynomial_coeff_two
#print axioms Universality.FiniteNetwork.integerComplementReliabilityPolynomial_coeff_two
#print axioms Universality.FiniteNetwork.integerFixedPointPolynomial_mod_two_nonconstant_of_parity
#print axioms Universality.FiniteNetwork.integerFixedPointPolynomial_mod_prime_nonconstant_of_mod_two

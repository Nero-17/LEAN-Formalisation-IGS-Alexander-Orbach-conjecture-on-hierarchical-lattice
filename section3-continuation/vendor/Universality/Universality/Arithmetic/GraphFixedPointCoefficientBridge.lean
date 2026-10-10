import Universality.Arithmetic.FixedPointIndexedGraph

/-!
The indexed deletion–contraction coefficient is exactly the coefficient of the
highest possible power in the original finite-network reliability polynomial.
This is an identity for every original finite network, including repeated
edges and isolated vertices; no canonicality or nonvanishing is assumed.
-/

namespace Universality.FiniteNetwork

noncomputable section
open scoped BigOperators
open Universality.Section4

variable {vertices edges : ℕ}

def toIndexedNetwork (network : FiniteNetwork vertices edges) :
    IndexedNetwork (Fin vertices) edges where
  endpoint := network.endpoint
  source := network.source
  target := network.target

@[simp] theorem toIndexedNetwork_openGraph (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    network.toIndexedNetwork.openGraph configuration = network.openGraph configuration := rfl

@[simp] theorem toIndexedNetwork_fullGraph (network : FiniteNetwork vertices edges) :
    network.toIndexedNetwork.fullGraph = network.fullGraph := rfl

theorem toIndexedNetwork_linked_iff_crosses (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    network.toIndexedNetwork.Linked configuration network.source network.target ↔
      network.crosses configuration = true := by
  rw [network.toIndexedNetwork.linked_iff_reachable,
    toIndexedNetwork_openGraph, network.crosses_eq_true]

theorem configuration_sign_product (configuration : Configuration edges) :
    (∏ edge : Fin edges, if configuration edge then (1 : ℤ) else -1) =
      (-1 : ℤ) ^ (edges - openCount configuration) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, one_mul]
  congr 1
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun edge : Fin edges => configuration edge = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  unfold openCount
  omega

theorem integerReliabilityPolynomial_coeff_edges_eq_signedCoefficient
    (network : FiniteNetwork vertices edges) :
    network.integerReliabilityPolynomial.coeff edges =
      network.toIndexedNetwork.signedCoefficient := by
  classical
  rw [network.integerReliabilityPolynomial_coeff_edges]
  unfold IndexedNetwork.signedCoefficient
  change _ = ∑ configuration : Configuration edges,
    if network.toIndexedNetwork.Linked configuration network.source network.target then
      ∏ edge : Fin edges, if configuration edge then (1 : ℤ) else -1
    else 0
  simp only [toIndexedNetwork_linked_iff_crosses,
    configuration_sign_product]

end
end Universality.FiniteNetwork

#print axioms Universality.FiniteNetwork.integerReliabilityPolynomial_coeff_edges_eq_signedCoefficient

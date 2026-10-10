import Universality.Arithmetic.GraphFixedPointCoefficientBridge
import Universality.Arithmetic.GraphIndexedVertexConnectivity
import Universality.Arithmetic.FixedPointCoefficientPositive

/-!
The full degree of the actual reliability polynomial and of its complete
fixed-point quotient. Canonical terminal paths provide the vertex-connectivity
input to signed-coefficient positivity. The indexed network retains every
original vertex and edge, so the top coefficient is the original coefficient.
-/

namespace Universality.FiniteNetwork

noncomputable section
open Universality.Section4 Polynomial
variable {vertices edges : ℕ}

theorem toIndexedNetwork_supportedOn (network : FiniteNetwork vertices edges) :
    network.toIndexedNetwork.SupportedOn Finset.univ := by
  exact ⟨Finset.mem_univ _, Finset.mem_univ _, fun _ =>
    ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩

theorem toIndexedNetwork_connectedOn (network : FiniteNetwork vertices edges)
    (hconnected : ∀ vertex, network.fullGraph.Reachable network.source vertex) :
    network.toIndexedNetwork.ConnectedOn Finset.univ := by
  intro vertex _
  exact (network.toIndexedNetwork.linked_iff_reachable (fun _ => true)
    network.source vertex).mpr (hconnected vertex)

@[simp] theorem toIndexedNetwork_augmentedGraph (network : FiniteNetwork vertices edges) :
    network.toIndexedNetwork.augmentedGraph = network.terminalAugmentedGraph := rfl

theorem integerFixedPointPolynomial_ne_zero
    (network : FiniteNetwork vertices edges)
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    network.integerFixedPointPolynomial hconnected ≠ 0 := by
  intro hzero
  have hvalue := network.integerFixedPointPolynomial_zero hconnected hscale
  norm_num [hzero] at hvalue

theorem integerFixedPointPolynomial_natDegree_add_two
    (network : FiniteNetwork vertices edges)
    (hconnected : network.fullGraph.Reachable network.source network.target)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    (network.integerFixedPointPolynomial hconnected).natDegree + 2 =
      network.integerReliabilityPolynomial.natDegree := by
  have hdegree := Section4.fixedPoint_natDegree network.reliabilityPolynomial
    ((network.integerFixedPointPolynomial hconnected).map (Int.castRingHom ℚ))
    (network.rationalFixedPointPolynomial_factor hconnected)
    (network.reliabilityPolynomial_natDegree_ge_two hconnected hscale)
    ((Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℚ))).mpr
      (network.integerFixedPointPolynomial_ne_zero hconnected hscale))
  rw [natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)),
    ← network.integerReliabilityPolynomial_map,
    natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ))] at hdegree
  exact hdegree

end
end Universality.FiniteNetwork

namespace Universality.Rule

noncomputable section
open FiniteNetwork Universality.Section4 Polynomial

theorem Classical.toIndexedNetwork_vertexConnectedOn {rule : Rule} (h : rule.Classical) :
    rule.network.toIndexedNetwork.VertexConnectedOn Finset.univ := by
  intro removed _
  change (rule.network.terminalAugmentedGraph.induce
    (↑(Finset.univ.erase removed) : Set (Fin rule.vertices))).Preconnected
  have hvertices : (↑(Finset.univ.erase removed) : Set (Fin rule.vertices)) =
      {vertex | vertex ≠ removed} := by
    ext vertex
    simp
  rw [hvertices]
  exact h.terminalAugmentedGraph_preconnected_delete_vertex removed

theorem Classical.indexed_normalizedCoefficient_pos {rule : Rule} (h : rule.Classical) :
    0 < rule.network.toIndexedNetwork.normalizedCoefficient Finset.univ :=
  IndexedNetwork.normalizedCoefficient_pos rule.network.toIndexedNetwork Finset.univ
    rule.network.toIndexedNetwork_supportedOn
    (rule.network.toIndexedNetwork_connectedOn h.connected)
    rule.network.loopless rule.network.terminals_distinct
    h.toIndexedNetwork_vertexConnectedOn

theorem Classical.integerReliabilityPolynomial_coeff_edges_ne_zero
    {rule : Rule} (h : rule.Classical) :
    rule.network.integerReliabilityPolynomial.coeff rule.edges ≠ 0 := by
  rw [rule.network.integerReliabilityPolynomial_coeff_edges_eq_signedCoefficient]
  intro hzero
  have hpositive := h.indexed_normalizedCoefficient_pos
  simp only [IndexedNetwork.normalizedCoefficient, hzero, mul_zero,
    lt_self_iff_false] at hpositive

theorem Classical.integerReliabilityPolynomial_natDegree
    {rule : Rule} (h : rule.Classical) :
    rule.network.integerReliabilityPolynomial.natDegree = rule.edges :=
  natDegree_eq_of_le_of_coeff_ne_zero
    rule.network.integerReliabilityPolynomial_natDegree_le_edges
    h.integerReliabilityPolynomial_coeff_edges_ne_zero

theorem Classical.reliabilityPolynomial_natDegree {rule : Rule} (h : rule.Classical) :
    rule.network.reliabilityPolynomial.natDegree = rule.edges := by
  rw [← rule.network.integerReliabilityPolynomial_map,
    natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ))]
  exact h.integerReliabilityPolynomial_natDegree

theorem Classical.integerFixedPointPolynomial_natDegree {rule : Rule} (h : rule.Classical) :
    (rule.network.integerFixedPointPolynomial (h.connected _)).natDegree = rule.edges - 2 := by
  have hdegree := rule.network.integerFixedPointPolynomial_natDegree_add_two
    (h.connected _) h.scale
  rw [h.integerReliabilityPolynomial_natDegree] at hdegree
  omega

theorem Classical.rationalFixedPointPolynomial_natDegree {rule : Rule} (h : rule.Classical) :
    ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom ℚ)).natDegree = rule.edges - 2 := by
  rw [natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ))]
  exact h.integerFixedPointPolynomial_natDegree

theorem Classical.integerFixedPointPolynomial_degree {rule : Rule} (h : rule.Classical) :
    (rule.network.integerFixedPointPolynomial (h.connected _)).degree =
      ((rule.edges - 2 : ℕ) : WithBot ℕ) := by
  rw [degree_eq_natDegree (rule.network.integerFixedPointPolynomial_ne_zero
    (h.connected _) h.scale), h.integerFixedPointPolynomial_natDegree]

end
end Universality.Rule

#print axioms Universality.Rule.Classical.toIndexedNetwork_vertexConnectedOn
#print axioms Universality.Rule.Classical.integerReliabilityPolynomial_natDegree
#print axioms Universality.Rule.Classical.integerFixedPointPolynomial_degree

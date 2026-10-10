import Universality.Percolation.SingleTerminalMeanRecursion
import Universality.Graph.ClassicalSubstitution

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem NetworkEquivalence.expectedInternalSourceMass
    {R : FiniteNetwork outerVertices outerEdges} {S : FiniteNetwork innerVertices innerEdges}
    (equivalence : R.NetworkEquivalence S) (p : ℝ) :
    S.expectedInternalSourceMass p = R.expectedInternalSourceMass p := by
  unfold FiniteNetwork.expectedInternalSourceMass
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.bernoulliWeight, equivalence.internalSelectedMass]

theorem expectedInternalSourceMass_disintegrate (R : FiniteNetwork vertices edges) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) :
    R.expectedInternalSourceMass p =
      R.reliability p * R.conditionalVertexMass p .connected +
        (1 - R.reliability p) * R.conditionalVertexMass p .single := by
  change _ = R.reliability p * R.conditionalInternalMean p true true false +
    (1 - R.reliability p) * R.conditionalInternalMean p false true false
  unfold expectedInternalSourceMass conditionalInternalMean
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro configuration _
  unfold conditionalCellWeight
  cases hcross : R.crosses configuration <;>
    simp only [hcross, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;>
    field_simp [hpositive.ne', (sub_pos.mpr hless).ne']
  all_goals ring

theorem expectedInternalSourceMass_pos (R : FiniteNetwork vertices edges)
    {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    0 < R.expectedInternalSourceMass p := by
  have hpositive := (R.reliability_pos_iff_connected hp hp').mpr hconnected
  have hless := R.reliability_lt_one hp hp'
  rw [R.expectedInternalSourceMass_disintegrate p hpositive hless]
  exact add_pos (mul_pos hpositive (R.conditionalVertexMass_pos hp hp' hconnected hscale _))
    (mul_pos (sub_pos.mpr hless) (R.conditionalVertexMass_pos hp hp' hconnected hscale _))

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem Classical.generation_source_mean_bounds {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (n : ℕ) :
    (rule.network.sourceIncidentEdges.card : ℝ) * (rule.generation n).network.expectedInternalSourceMass p ≤
        (rule.generation (n + 1)).network.expectedInternalSourceMass p ∧
      (rule.generation (n + 1)).network.expectedInternalSourceMass p ≤
        (rule.network.sourceIncidentEdges.card : ℝ) * (rule.generation n).network.expectedInternalSourceMass p +
          ((rule.generation (n + 1)).vertices : ℝ) *
            ((rule.edges : ℝ) * (rule.generation n).network.reliability p) := by
  obtain ⟨symmetry, hs, ht⟩ := (h.generation n).massAdmissible.symmetric
  have hb := rule.network.expectedInternalSourceMass_substitute_bounds
    (rule.generation n).network symmetry hs ht hp hp'
  have hvertices : Fintype.card (rule.network.SubstitutionVertex (rule.generation n).network) =
      (rule.generation (n + 1)).vertices := by
    have hi := Fintype.card_congr (rule.generationTopDecomposition n).vertex
    simpa only [Fintype.card_fin] using hi.symm
  simpa only [(rule.generationTopDecomposition n).expectedInternalSourceMass, hvertices] using hb

end
end Universality.Rule

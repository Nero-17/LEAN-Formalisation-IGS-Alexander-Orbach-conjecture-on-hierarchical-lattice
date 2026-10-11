import Universality.Percolation.SingleTerminalMomentPathwise

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def expectedInternalSourceMoment (R : FiniteNetwork vertices edges) (p : ℝ) (order : ℕ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * (R.internalSelectedMass true false configuration : ℝ) ^ order

theorem expectedInternalSourceMoment_nonneg (R : FiniteNetwork vertices edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) : 0 ≤ R.expectedInternalSourceMoment p order := by
  exact Finset.sum_nonneg (fun configuration _ =>
    mul_nonneg (bernoulliWeight_nonneg hp hp' _) (pow_nonneg (Nat.cast_nonneg _) _))

theorem NetworkSymmetry.expectedInternalTargetMoment {R : FiniteNetwork vertices edges}
    (symmetry : R.NetworkSymmetry) (hs : symmetry.vertex R.source = R.target)
    (ht : symmetry.vertex R.target = R.source) (p : ℝ) (order : ℕ) :
    (∑ configuration, bernoulliWeight p configuration * (R.internalSelectedMass false true configuration : ℝ) ^ order) =
      R.expectedInternalSourceMoment p order := by
  unfold expectedInternalSourceMoment
  rw [← symmetry.configurationEquiv.sum_comp]
  simp only [symmetry.bernoulliWeight_configuration,
    symmetry.internalSelectedMass_configuration hs ht]

theorem sourceIncidentChildPower_expectation
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (symmetry : S.NetworkSymmetry) (hs : symmetry.vertex S.source = S.target)
    (ht : symmetry.vertex S.target = S.source) (p : ℝ) (order : ℕ) :
    (∑ configuration : Fin outerEdges → Configuration innerEdges,
      (∏ edge, bernoulliWeight p (configuration edge)) * R.sourceIncidentChildPower S configuration order) =
      (R.sourceIncidentEdges.card : ℝ) * S.expectedInternalSourceMoment p order := by
  simp only [sourceIncidentChildPower, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (edge : Fin outerEdges) :
      (∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ e, bernoulliWeight p (configuration e)) *
          (if (R.endpoint edge).1 = R.source then (S.internalSelectedMass true false (configuration edge) : ℝ)
          else S.internalSelectedMass false true (configuration edge)) ^ order) =
      S.expectedInternalSourceMoment p order := by
    rw [finite_product_local_moment
      (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
      (fun cell => (if (R.endpoint edge).1 = R.source then (S.internalSelectedMass true false cell : ℝ)
        else S.internalSelectedMass false true cell) ^ order) edge]
    simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul]
    by_cases hfirst : (R.endpoint edge).1 = R.source
    · simp only [hfirst, ↓reduceIte, expectedInternalSourceMoment]
    · simpa only [hfirst, ↓reduceIte] using symmetry.expectedInternalTargetMoment hs ht p order
  simp only [hlocal, Finset.sum_const, nsmul_eq_mul]

theorem expectedInternalSourceMoment_substitute_le
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (symmetry : S.NetworkSymmetry) (hs : symmetry.vertex S.source = S.target)
    (ht : symmetry.vertex S.target = S.source) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (order : ℕ) (horder : 1 ≤ order) :
    (R.substitute S).expectedInternalSourceMoment p order ≤
      (R.sourceIncidentEdges.card : ℝ) ^ order * S.expectedInternalSourceMoment p order +
        (Fintype.card (R.SubstitutionVertex S) : ℝ) ^ order * ((outerEdges : ℝ) * S.reliability p) := by
  have hpower : (R.sourceIncidentEdges.card : ℝ) ^ order * S.expectedInternalSourceMoment p order =
      (R.sourceIncidentEdges.card : ℝ) ^ (order - 1) *
        ((R.sourceIncidentEdges.card : ℝ) * S.expectedInternalSourceMoment p order) := by
    rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel horder]
  rw [hpower, ← R.sourceIncidentChildPower_expectation S symmetry hs ht p order,
    ← S.child_crossing_count_expectation (outerEdges := outerEdges) p]
  unfold expectedInternalSourceMoment
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [bernoulliWeight_substitutionConfiguration]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro configuration _
  have hweight : 0 ≤ ∏ edge, bernoulliWeight p (configuration edge) :=
    Finset.prod_nonneg (fun edge _ => bernoulliWeight_nonneg hp hp' (configuration edge))
  have hb := mul_le_mul_of_nonneg_left
    (R.internalSelectedMass_substitute_pow_le_incident_add_crossings S configuration order horder) hweight
  convert hb using 1 <;> ring

theorem NetworkEquivalence.expectedInternalSourceMoment
    {R : FiniteNetwork outerVertices outerEdges} {S : FiniteNetwork innerVertices innerEdges}
    (equivalence : R.NetworkEquivalence S) (p : ℝ) (order : ℕ) :
    S.expectedInternalSourceMoment p order = R.expectedInternalSourceMoment p order := by
  unfold FiniteNetwork.expectedInternalSourceMoment
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.bernoulliWeight, equivalence.internalSelectedMass]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem Classical.generation_source_moment_le {rule : Rule} (h : rule.Classical)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) (horder : 1 ≤ order) (n : ℕ) :
    (rule.generation (n + 1)).network.expectedInternalSourceMoment p order ≤
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ order *
        (rule.generation n).network.expectedInternalSourceMoment p order +
          ((rule.generation (n + 1)).vertices : ℝ) ^ order *
            ((rule.edges : ℝ) * (rule.generation n).network.reliability p) := by
  obtain ⟨symmetry, hs, ht⟩ := (h.generation n).massAdmissible.symmetric
  have hb := rule.network.expectedInternalSourceMoment_substitute_le
    (rule.generation n).network symmetry hs ht hp hp' order horder
  have hvertices : Fintype.card (rule.network.SubstitutionVertex (rule.generation n).network) =
      (rule.generation (n + 1)).vertices := by
    have hi := Fintype.card_congr (rule.generationTopDecomposition n).vertex
    simpa only [Fintype.card_fin] using hi.symm
  simpa only [(rule.generationTopDecomposition n).expectedInternalSourceMoment, hvertices,
    rule.network.sourceIncidentEdges_card_eq_degree h.simple] using hb

end
end Universality.Rule

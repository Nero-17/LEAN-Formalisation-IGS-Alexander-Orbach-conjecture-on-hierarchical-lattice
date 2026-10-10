import Universality.Percolation.SingleTerminalCellMass
import Universality.Graph.IncidentDegree

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def expectedInternalSourceMass (R : FiniteNetwork vertices edges) (p : ℝ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration * R.internalSelectedMass true false configuration

theorem expectedInternalSourceMass_nonneg (R : FiniteNetwork vertices edges)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ R.expectedInternalSourceMass p := by
  exact Finset.sum_nonneg (fun configuration _ =>
    mul_nonneg (bernoulliWeight_nonneg hp hp' _) (Nat.cast_nonneg _))

theorem NetworkSymmetry.expectedInternalTargetMass {R : FiniteNetwork vertices edges}
    (symmetry : R.NetworkSymmetry) (hs : symmetry.vertex R.source = R.target)
    (ht : symmetry.vertex R.target = R.source) (p : ℝ) :
    (∑ configuration, bernoulliWeight p configuration * R.internalSelectedMass false true configuration) =
      R.expectedInternalSourceMass p := by
  unfold expectedInternalSourceMass
  rw [← symmetry.configurationEquiv.sum_comp]
  simp only [symmetry.bernoulliWeight_configuration,
    symmetry.internalSelectedMass_configuration hs ht]

theorem sourceIncidentChildMass_expectation
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (symmetry : S.NetworkSymmetry) (hs : symmetry.vertex S.source = S.target)
    (ht : symmetry.vertex S.target = S.source) (p : ℝ) :
    (∑ configuration : Fin outerEdges → Configuration innerEdges,
      (∏ edge, bernoulliWeight p (configuration edge)) * (R.sourceIncidentChildMass S configuration : ℝ)) =
      (R.sourceIncidentEdges.card : ℝ) * S.expectedInternalSourceMass p := by
  simp only [sourceIncidentChildMass, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (edge : Fin outerEdges) :
      (∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ e, bernoulliWeight p (configuration e)) *
          (if (R.endpoint edge).1 = R.source then (S.internalSelectedMass true false (configuration edge) : ℝ)
          else if (R.endpoint edge).2 = R.source then (S.internalSelectedMass false true (configuration edge) : ℝ)
          else 0)) =
      if edge ∈ R.sourceIncidentEdges then S.expectedInternalSourceMass p else 0 := by
    rw [finite_product_local_moment
      (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
      (fun cell => if (R.endpoint edge).1 = R.source then (S.internalSelectedMass true false cell : ℝ)
        else if (R.endpoint edge).2 = R.source then (S.internalSelectedMass false true cell : ℝ) else 0) edge]
    simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul]
    by_cases hfirst : (R.endpoint edge).1 = R.source
    · simp [hfirst, sourceIncidentEdges, expectedInternalSourceMass]
    · by_cases hsecond : (R.endpoint edge).2 = R.source
      · simpa only [hfirst, hsecond, sourceIncidentEdges, Finset.mem_filter, Finset.mem_univ,
          true_and, or_true, ↓reduceIte] using symmetry.expectedInternalTargetMass hs ht p
      · simp [hfirst, hsecond, sourceIncidentEdges]
  simp only [hlocal, ← Finset.sum_filter]
  simp

theorem child_crossing_count_expectation
    (S : FiniteNetwork innerVertices innerEdges) (p : ℝ) :
    (∑ configuration : Fin outerEdges → Configuration innerEdges,
      (∏ edge, bernoulliWeight p (configuration edge)) *
        ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (1 : ℝ) else 0) =
      (outerEdges : ℝ) * S.reliability p := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (edge : Fin outerEdges) :
      (∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ e, bernoulliWeight p (configuration e)) *
          (if S.crosses (configuration edge) then (1 : ℝ) else 0)) = S.reliability p := by
    rw [finite_product_local_moment
      (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
      (fun cell => if S.crosses cell then (1 : ℝ) else 0) edge]
    simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul, mul_ite, mul_one, mul_zero]
    rfl
  simp only [hlocal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem expectedInternalSourceMass_substitute_bounds
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (symmetry : S.NetworkSymmetry) (hs : symmetry.vertex S.source = S.target)
    (ht : symmetry.vertex S.target = S.source) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (R.sourceIncidentEdges.card : ℝ) * S.expectedInternalSourceMass p ≤
        (R.substitute S).expectedInternalSourceMass p ∧
      (R.substitute S).expectedInternalSourceMass p ≤
        (R.sourceIncidentEdges.card : ℝ) * S.expectedInternalSourceMass p +
          (Fintype.card (R.SubstitutionVertex S) : ℝ) * ((outerEdges : ℝ) * S.reliability p) := by
  have hmean : (R.substitute S).expectedInternalSourceMass p =
      ∑ configuration : Fin outerEdges → Configuration innerEdges,
        (∏ edge, bernoulliWeight p (configuration edge)) *
          ((R.substitute S).internalSelectedMass true false (substitutionConfigurationEquiv configuration) : ℝ) := by
    unfold expectedInternalSourceMass
    rw [← substitutionConfigurationEquiv.sum_comp]
    simp only [bernoulliWeight_substitutionConfiguration]
  rw [hmean, ← R.sourceIncidentChildMass_expectation S symmetry hs ht p,
    ← S.child_crossing_count_expectation (outerEdges := outerEdges) p]
  constructor
  · apply Finset.sum_le_sum
    intro configuration _
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast R.sourceIncidentChildMass_le_substitute S configuration)
      (Finset.prod_nonneg (fun edge _ => bernoulliWeight_nonneg hp hp' _))
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro configuration _
    have hpoint := R.internalSelectedMass_substitute_le_incident_add_failures S configuration
    have hreal : ((R.substitute S).internalSelectedMass true false (substitutionConfigurationEquiv configuration) : ℝ) ≤
        (R.sourceIncidentChildMass S configuration : ℝ) +
          (Fintype.card (R.SubstitutionVertex S) : ℝ) *
            ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (1 : ℝ) else 0 := by
      exact_mod_cast hpoint
    have hweight : 0 ≤ ∏ edge, bernoulliWeight p (configuration edge) :=
      Finset.prod_nonneg (fun edge _ => bernoulliWeight_nonneg hp hp' (configuration edge))
    have hweighted := mul_le_mul_of_nonneg_left hreal hweight
    convert hweighted using 1 <;> ring

end
end Universality.FiniteNetwork

import Universality.Percolation.AnnealedBirthMomentLower

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem internalSelectedMass_mono_selection (R : FiniteNetwork vertices edges)
    (firstSource firstTarget secondSource secondTarget : Bool) (configuration : Configuration edges)
    (hsource : firstSource = true → secondSource = true)
    (htarget : firstTarget = true → secondTarget = true) :
    R.internalSelectedMass firstSource firstTarget configuration ≤
      R.internalSelectedMass secondSource secondTarget configuration := by
  unfold internalSelectedMass
  apply Finset.sum_le_sum
  intro vertex _
  by_cases hactive : R.selectedActive firstSource firstTarget configuration vertex.val = true
  · have hactive' : R.selectedActive secondSource secondTarget configuration vertex.val = true := by
      simp only [selectedActive, Bool.or_eq_true, Bool.and_eq_true] at hactive ⊢
      exact hactive.elim (fun h => Or.inl ⟨hsource h.1, h.2⟩)
        (fun h => Or.inr ⟨htarget h.1, h.2⟩)
    simp [hactive, hactive']
  · simp only [hactive, ↓reduceIte]
    exact Nat.zero_le _

def sourceIncidentChildMass (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (configuration : Fin outerEdges → Configuration innerEdges) : ℕ :=
  ∑ edge : Fin outerEdges,
    if (R.endpoint edge).1 = R.source then S.internalSelectedMass true false (configuration edge)
    else if (R.endpoint edge).2 = R.source then S.internalSelectedMass false true (configuration edge) else 0

theorem internalSelectedMass_source_all_closed (R : FiniteNetwork vertices edges) :
    R.internalSelectedMass true false (fun _ => false) = 0 := by
  unfold internalSelectedMass
  apply Finset.sum_eq_zero
  intro vertex _
  simp [selectedActive, R.reachableDecide_all_closed, vertex.property.1.symm]

theorem sourceIncidentChildMass_le_substitute
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges) :
    R.sourceIncidentChildMass S configuration ≤
      (R.substitute S).internalSelectedMass true false (substitutionConfigurationEquiv configuration) := by
  rw [R.internalSelectedMass_substitute]
  apply le_trans _ (Nat.le_add_left _ _)
  unfold sourceIncidentChildMass
  apply Finset.sum_le_sum
  intro edge _
  simp only [internalStateMass, orientedChildState, orientedStateOf_sourceSelected,
    orientedStateOf_targetSelected]
  have hactive : R.selectedActive true false (S.coarseConfiguration configuration) R.source = true := by
    simp only [selectedActive, Bool.true_and, Bool.false_and, Bool.or_false,
      SimpleGraph.reachableDecide_eq_true]
    exact SimpleGraph.Reachable.refl _
  by_cases hfirst : (R.endpoint edge).1 = R.source
  · rw [if_pos hfirst, hfirst, hactive]
    exact S.internalSelectedMass_mono_selection true false true _ _ (fun _ => rfl) (by simp)
  · rw [if_neg hfirst]
    by_cases hsecond : (R.endpoint edge).2 = R.source
    · rw [if_pos hsecond, hsecond, hactive]
      exact S.internalSelectedMass_mono_selection false true _ true _ (by simp) (fun _ => rfl)
    · rw [if_neg hsecond]
      exact Nat.zero_le _

theorem internalSelectedMass_substitute_all_child_failures
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (hfail : ∀ edge, S.crosses (configuration edge) = false) :
    (R.substitute S).internalSelectedMass true false (substitutionConfigurationEquiv configuration) =
      R.sourceIncidentChildMass S configuration := by
  have hcoarse : S.coarseConfiguration configuration = fun _ => false := by
    funext edge
    exact hfail edge
  rw [R.internalSelectedMass_substitute, hcoarse, R.internalSelectedMass_source_all_closed, zero_add]
  unfold sourceIncidentChildMass
  apply Finset.sum_congr rfl
  intro edge _
  simp only [internalStateMass, orientedChildState, orientedStateOf_sourceSelected,
    orientedStateOf_targetSelected, selectedActive, Bool.true_and, Bool.false_and,
    Bool.or_false, R.reachableDecide_all_closed]
  by_cases hfirst : (R.endpoint edge).1 = R.source
  · have hsecond : (R.endpoint edge).2 ≠ R.source := by
      intro heq
      exact R.loopless edge (hfirst.trans heq.symm)
    simp [hfirst, hsecond, hsecond.symm]
  · by_cases hsecond : (R.endpoint edge).2 = R.source
    · simp [hfirst, Ne.symm hfirst, hsecond]
    · simp [hfirst, Ne.symm hfirst, hsecond, Ne.symm hsecond, internalSelectedMass, selectedActive]

theorem internalSelectedMass_substitute_le_incident_add_failures
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges) :
    (R.substitute S).internalSelectedMass true false (substitutionConfigurationEquiv configuration) ≤
      R.sourceIncidentChildMass S configuration + Fintype.card (R.SubstitutionVertex S) *
        ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (1 : ℕ) else 0 := by
  by_cases hfail : ∀ edge, S.crosses (configuration edge) = false
  · rw [R.internalSelectedMass_substitute_all_child_failures S configuration hfail]
    exact Nat.le_add_right _ _
  · push Not at hfail
    obtain ⟨edge, hedge⟩ := hfail
    have hcross : S.crosses (configuration edge) = true := by
      cases hstate : S.crosses (configuration edge) <;> simp_all
    have hsum : 1 ≤ ∑ e : Fin outerEdges, if S.crosses (configuration e) then (1 : ℕ) else 0 := by
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun e : Fin outerEdges => if S.crosses (configuration e) then (1 : ℕ) else 0)
        (fun e _ => Nat.zero_le _) (Finset.mem_univ edge)
      simpa only [hcross, ↓reduceIte] using hs
    have hbound := (R.substitute S).internalSelectedMass_le true false (substitutionConfigurationEquiv configuration)
    have hcard : Fintype.card (R.substitute S).InteriorVertex ≤ Fintype.card (R.SubstitutionVertex S) := by
      rw [(R.substitute S).card_interior_vertices]
      exact Nat.sub_le _ _
    exact (hbound.trans hcard).trans ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_left _ _))

end
end Universality.FiniteNetwork

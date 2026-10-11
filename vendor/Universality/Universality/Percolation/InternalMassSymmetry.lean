import Universality.Percolation.InternalMassLaw

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} {R : FiniteNetwork vertices edges}

def NetworkSymmetry.internalVertexEquiv (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    R.InteriorVertex ≃ R.InteriorVertex :=
  symmetry.vertex.subtypeEquiv (by
    intro v
    change (v ≠ R.source ∧ v ≠ R.target) ↔
      (symmetry.vertex v ≠ R.source ∧ symmetry.vertex v ≠ R.target)
    rw [← ht, ← hs, symmetry.vertex.injective.ne_iff, symmetry.vertex.injective.ne_iff]
    simp only [hs, ht]
    exact and_comm)

theorem NetworkSymmetry.selectedActive_configuration (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) (v : Fin vertices) :
    R.selectedActive sourceSelected targetSelected (symmetry.configurationEquiv ω) (symmetry.vertex v) =
      R.selectedActive targetSelected sourceSelected ω v := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedActive, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true]
  conv_lhs => rw [← ht, ← hs, symmetry.reachable_configuration_iff,
    symmetry.reachable_configuration_iff]
  rw [hs]
  tauto

theorem NetworkSymmetry.internalSelectedMass_configuration (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) :
    R.internalSelectedMass sourceSelected targetSelected (symmetry.configurationEquiv ω) =
      R.internalSelectedMass targetSelected sourceSelected ω := by
  unfold internalSelectedMass
  rw [← (symmetry.internalVertexEquiv hs ht).sum_comp]
  apply Finset.sum_congr rfl
  intro v _
  change (if R.selectedActive sourceSelected targetSelected (symmetry.configurationEquiv ω)
    (symmetry.vertex v.val) then 1 else 0) = _
  rw [symmetry.selectedActive_configuration hs ht]

theorem NetworkSymmetry.conditionalInternalMean_swap (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) :
    R.conditionalInternalMean p opened sourceSelected targetSelected =
      R.conditionalInternalMean p opened targetSelected sourceSelected := by
  unfold conditionalInternalMean
  rw [← symmetry.configurationEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  rw [symmetry.conditionalCellWeight R hs ht,
    symmetry.internalSelectedMass_configuration hs ht]

theorem NetworkSymmetry.conditionalInternalPGF_swap (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) (z : ℝ) :
    R.conditionalInternalPGF p opened sourceSelected targetSelected z =
      R.conditionalInternalPGF p opened targetSelected sourceSelected z := by
  unfold conditionalInternalPGF
  rw [← symmetry.configurationEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  rw [symmetry.conditionalCellWeight R hs ht,
    symmetry.internalSelectedMass_configuration hs ht]

theorem selectedActive_connected (R : FiniteNetwork vertices edges)
    (ω : Configuration edges) (hcross : R.crosses ω = true) (v : Fin vertices) :
    R.selectedActive true true ω v = R.selectedActive true false ω v := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedActive, Bool.true_and, Bool.false_and, Bool.or_false,
    Bool.or_eq_true, SimpleGraph.reachableDecide_eq_true]
  have h := (R.crosses_eq_true ω).mp hcross
  exact ⟨fun hv => hv.elim id (fun ht => h.trans ht), Or.inl⟩

theorem internalSelectedMass_connected (R : FiniteNetwork vertices edges)
    (ω : Configuration edges) (hcross : R.crosses ω = true) :
    R.internalSelectedMass true true ω = R.internalSelectedMass true false ω := by
  unfold internalSelectedMass
  simp_rw [R.selectedActive_connected ω hcross]

theorem conditionalInternalMean_connected (R : FiniteNetwork vertices edges) (p : ℝ) :
    R.conditionalInternalMean p true true true = R.conditionalInternalMean p true true false := by
  unfold conditionalInternalMean
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hcross : R.crosses ω = true
  · rw [R.internalSelectedMass_connected ω hcross]
  · simp [conditionalCellWeight, hcross]

end
end Universality.FiniteNetwork

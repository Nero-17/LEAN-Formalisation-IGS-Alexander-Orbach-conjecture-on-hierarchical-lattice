import Universality.Graph.NetworkEquivalence
import Universality.Percolation.InternalMassMoments

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
set_option maxHeartbeats 0
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
variable (equivalence : R.NetworkEquivalence S)

def interior : R.InteriorVertex ≃ S.InteriorVertex :=
  equivalence.vertex.subtypeEquiv (by
    intro vertex
    change (vertex ≠ R.source ∧ vertex ≠ R.target) ↔
      (equivalence.vertex vertex ≠ S.source ∧ equivalence.vertex vertex ≠ S.target)
    constructor
    · rintro ⟨hs, ht⟩
      exact ⟨fun h => hs (equivalence.vertex.injective (h.trans equivalence.source.symm)),
        fun h => ht (equivalence.vertex.injective (h.trans equivalence.target.symm))⟩
    · rintro ⟨hs, ht⟩
      exact ⟨fun h => hs ((congrArg equivalence.vertex h).trans equivalence.source),
        fun h => ht ((congrArg equivalence.vertex h).trans equivalence.target)⟩)

theorem selectedActive (sourceSelected targetSelected : Bool) (ω : Configuration eR) (vertex : Fin vR) :
    S.selectedActive sourceSelected targetSelected (equivalence.configuration ω) (equivalence.vertex vertex) =
      R.selectedActive sourceSelected targetSelected ω vertex := by
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteNetwork.selectedActive, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true]
  have hreach (u v : Fin vR) : (S.openGraph (equivalence.configuration ω)).Reachable
      (equivalence.vertex u) (equivalence.vertex v) ↔ (R.openGraph ω).Reachable u v :=
    (equivalence.openGraphIso ω).reachable_iff
  rw [← equivalence.source, ← equivalence.target, hreach, hreach]

theorem internalSelectedMass (sourceSelected targetSelected : Bool) (ω : Configuration eR) :
    S.internalSelectedMass sourceSelected targetSelected (equivalence.configuration ω) =
      R.internalSelectedMass sourceSelected targetSelected ω := by
  unfold FiniteNetwork.internalSelectedMass
  rw [← equivalence.interior.sum_comp]
  apply Finset.sum_congr rfl
  intro vertex _
  change (if S.selectedActive sourceSelected targetSelected (equivalence.configuration ω)
    (equivalence.vertex vertex.val) then 1 else 0) = _
  rw [equivalence.selectedActive]

theorem conditionalCellWeight (p : ℝ) (opened : Bool) (ω : Configuration eR) :
    S.conditionalCellWeight p opened (equivalence.configuration ω) = R.conditionalCellWeight p opened ω := by
  unfold FiniteNetwork.conditionalCellWeight
  rw [equivalence.crosses, equivalence.bernoulliWeight, equivalence.reliability]

include equivalence in
theorem conditionalInternalMoment (p : ℝ) (opened sourceSelected targetSelected : Bool) (r : ℕ) :
    S.conditionalInternalMoment p opened sourceSelected targetSelected r =
      R.conditionalInternalMoment p opened sourceSelected targetSelected r := by
  unfold FiniteNetwork.conditionalInternalMoment
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.conditionalCellWeight, equivalence.internalSelectedMass]

end
end Universality.FiniteNetwork.NetworkEquivalence

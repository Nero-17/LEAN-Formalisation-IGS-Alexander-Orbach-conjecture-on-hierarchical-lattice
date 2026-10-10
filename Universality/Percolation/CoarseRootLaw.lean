import Universality.Percolation.CoarseRootMass
import Universality.Percolation.ConditionalMassAtomOrientation
import Universality.Percolation.BirthExpectations

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem rootChildState_endpoints_eq_of_open (R : FiniteNetwork vertices edges)
    (root : Fin vertices) (coarse : Configuration edges) (edge : Fin edges) (hopen : coarse edge = true) :
    (R.openGraph coarse).reachableDecide root (R.endpoint edge).1 =
      (R.openGraph coarse).reachableDecide root (R.endpoint edge).2 := by
  have hadj : (R.openGraph coarse).Adj (R.endpoint edge).1 (R.endpoint edge).2 :=
    ⟨R.loopless edge, edge, hopen, Or.inl rfl⟩
  apply Bool.eq_iff_iff.mpr
  simp only [SimpleGraph.reachableDecide_eq_true]
  exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩

theorem live_rootChildState_determines_crossing (R : FiniteNetwork vertices edges)
    (root : Fin vertices) (coarse : Configuration edges) (edge : Fin edges)
    (hlive : R.rootChildState root coarse edge ≠ .inactive) :
    (R.rootChildState root coarse edge = .connected ↔ coarse edge = true) := by
  by_cases hopen : coarse edge = true
  · have heq := R.rootChildState_endpoints_eq_of_open root coarse edge hopen
    unfold rootChildState orientedStateOf at hlive ⊢
    rw [← heq, hopen] at hlive ⊢
    cases ha : (R.openGraph coarse).reachableDecide root (R.endpoint edge).1 <;> simp_all
  · have hclosed : coarse edge = false := Bool.eq_false_iff.mpr hopen
    simp only [rootChildState, orientedStateOf, hclosed]
    cases (R.openGraph coarse).reachableDecide root (R.endpoint edge).1 <;>
      cases (R.openGraph coarse).reachableDecide root (R.endpoint edge).2 <;> simp

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem coarse_substitution_observable (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (response : Configuration outerEdges → (Fin outerEdges → Configuration innerEdges) → ℝ) :
    (∑ cells, (∏ edge, bernoulliWeight p (cells edge)) * response (S.coarseConfiguration cells) cells) =
      ∑ coarse, bernoulliWeight (S.reliability p) coarse *
        ∑ cells, (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) * response coarse cells := by
  have hweight (coarse : Configuration outerEdges) (cells : Fin outerEdges → Configuration innerEdges) :
      bernoulliWeight (S.reliability p) coarse *
        (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) =
      if S.coarseConfiguration cells = coarse then ∏ edge, bernoulliWeight p (cells edge) else 0 := by
    rw [← S.coarse_fiber_conditional_joint_weight p coarse cells]
    field_simp [ne_of_gt (bernoulliWeight_pos hpositive hless coarse)]
  symm
  simp only [Finset.mul_sum, ← mul_assoc]
  simp_rw [hweight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cells _
  simp only [ite_mul, zero_mul]
  simp

def coarseRootMassObservable (p : ℝ) (root : Fin outerVertices) (response : ℕ → ℝ) : ℝ :=
  ∑ configuration : Configuration (outerEdges * innerEdges), bernoulliWeight p configuration *
    response (((R.substitute S).clusterVertices configuration
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card)

theorem coarseRootMassObservable_disintegration (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (root : Fin outerVertices) (response : ℕ → ℝ) :
    R.coarseRootMassObservable S p root response =
      ∑ coarse, bernoulliWeight (S.reliability p) coarse *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) *
            response ((R.clusterVertices coarse root).card +
              ∑ edge, S.internalStateMass (R.rootChildState root coarse edge) (cells edge)) := by
  unfold coarseRootMassObservable
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [bernoulliWeight_substitutionConfiguration, R.coarseRoot_cluster_mass S]
  exact S.coarse_substitution_observable p hpositive hless
    (fun coarse cells => response ((R.clusterVertices coarse root).card +
      ∑ edge, S.internalStateMass (R.rootChildState root coarse edge) (cells edge)))

theorem root_child_conditional_mass_probability
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (root : Fin outerVertices) (coarse : Configuration outerEdges) (edge : Fin outerEdges)
    (child : LiveState) (hchild : (R.rootChildState root coarse edge).eraseOrientation = some child)
    (size : ℕ) :
    S.conditionalInternalMassProbability p (coarse edge)
      (R.rootChildState root coarse edge).sourceSelected
      (R.rootChildState root coarse edge).targetSelected size =
    S.conditionalInternalMassProbability p (child == .connected) true (child == .both) size := by
  apply S.conditional_mass_probability_eq_of_characteristic_eq
  intro t
  have heq := S.conditionalInternalCharacteristic_oriented symmetry hs ht p hpositive hless
    (R.rootChildState root coarse edge) (coarse edge) t
    (fun hlive => R.live_rootChildState_determines_crossing root coarse edge hlive)
  simpa only [hchild, conditionalVertexCharacteristic] using heq

end
end Universality.FiniteNetwork





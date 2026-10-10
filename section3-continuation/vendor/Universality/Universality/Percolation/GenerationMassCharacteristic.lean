import Universality.Percolation.ConditionalMassCharacteristic
import Universality.Percolation.VertexMomentRecursion

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def conditionalVertexCharacteristic (R : FiniteNetwork vertices edges) (p : ℝ)
    (state : LiveState) (t : ℝ) : ℂ :=
  R.conditionalInternalCharacteristic p (state == .connected) true (state == .both) t

theorem conditionalInternalCharacteristic_oriented (R : FiniteNetwork vertices edges)
    (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (parent : OrientedState) (opened : Bool) (t : ℝ)
    (hstate : parent ≠ .inactive → (parent = .connected ↔ opened = true)) :
    R.conditionalInternalCharacteristic p opened parent.sourceSelected parent.targetSelected t =
      match parent.eraseOrientation with
      | none => 1
      | some state => R.conditionalVertexCharacteristic p state t := by
  cases parent with
  | inactive => exact R.conditionalInternalCharacteristic_inactive p hpositive hless opened t
  | connected =>
    have hopen : opened = true := (hstate (by decide)).mp rfl
    subst opened
    exact R.conditionalInternalCharacteristic_connected p t
  | both =>
    have hopen : opened = false := by
      cases opened <;> first | rfl | simp at hstate
    subst opened
    rfl
  | sourceOnly =>
    have hopen : opened = false := by
      cases opened <;> first | rfl | simp at hstate
    subst opened
    rfl
  | targetOnly =>
    have hopen : opened = false := by
      cases opened <;> first | rfl | simp at hstate
    subst opened
    exact symmetry.conditionalInternalCharacteristic_swap hs ht p false false true t

theorem child_conditionalVertexCharacteristic
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (state : LiveState) (coarse : Configuration outerEdges) (edge : Fin outerEdges) (t : ℝ) :
    S.conditionalInternalCharacteristic p (coarse edge)
      (R.orientedChildState true (state == .both) coarse edge).sourceSelected
      (R.orientedChildState true (state == .both) coarse edge).targetSelected t =
      match R.childState state coarse edge with
      | none => 1
      | some child => S.conditionalVertexCharacteristic p child t := by
  rw [S.conditionalInternalCharacteristic_oriented symmetry hs ht p hpositive hless _ (coarse edge) t
    (fun hlive => R.live_oriented_state_determines_crossing true (state == .both) coarse edge hlive),
    R.eraseOrientation_orientedChildState]

end
end Universality.FiniteNetwork

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}

theorem conditionalInternalCharacteristic (equivalence : R.NetworkEquivalence S)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) (t : ℝ) :
    S.conditionalInternalCharacteristic p opened sourceSelected targetSelected t =
      R.conditionalInternalCharacteristic p opened sourceSelected targetSelected t := by
  unfold FiniteNetwork.conditionalInternalCharacteristic
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.conditionalCellWeight, equivalence.internalSelectedMass]

end
end Universality.FiniteNetwork.NetworkEquivalence

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem generation_conditionalInternalCharacteristic (rule : Rule) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (opened sourceSelected targetSelected : Bool) (t : ℝ) :
    (rule.generation (n + 1)).network.conditionalInternalCharacteristic p opened sourceSelected targetSelected t =
      ∑ coarse, (rule.network.conditionalCellWeight p opened coarse : ℂ) *
        Complex.exp ((t * rule.network.internalSelectedMass sourceSelected targetSelected coarse : ℝ) * Complex.I) *
          ∏ e, (rule.generation n).network.conditionalInternalCharacteristic p (coarse e)
            (rule.network.orientedChildState sourceSelected targetSelected coarse e).sourceSelected
            (rule.network.orientedChildState sourceSelected targetSelected coarse e).targetSelected t := by
  rw [← (rule.generationTopDecomposition n).conditionalInternalCharacteristic]
  rw [rule.network.conditionalInternalCharacteristic_substitute (rule.generation n).network p
    (by rwa [rule.generation_fixed_point p hfixed n])
    (by rwa [rule.generation_fixed_point p hfixed n]), rule.generation_fixed_point p hfixed n]

theorem generation_conditionalVertexCharacteristic (rule : Rule) (hsymmetric : rule.TerminalSymmetric)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (state : LiveState) (t : ℝ) :
    (rule.generation (n + 1)).network.conditionalVertexCharacteristic p state t =
      ∑ coarse, (rule.network.conditionalCellWeight p (state == .connected) coarse : ℂ) *
        Complex.exp ((t * rule.network.internalSelectedMass true (state == .both) coarse : ℝ) * Complex.I) *
          ∏ e, match rule.network.childState state coarse e with
            | none => 1
            | some child => (rule.generation n).network.conditionalVertexCharacteristic p child t := by
  obtain ⟨symmetry, hs, ht⟩ := hsymmetric.generation n
  unfold conditionalVertexCharacteristic
  rw [rule.generation_conditionalInternalCharacteristic p hp hp' hfixed n]
  simp_rw [rule.network.child_conditionalVertexCharacteristic (rule.generation n).network symmetry hs ht p
    (by rwa [rule.generation_fixed_point p hfixed n])
    (by rwa [rule.generation_fixed_point p hfixed n])]
  rfl

end
end Universality.Rule

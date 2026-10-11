import Universality.Percolation.ConditionalMassInversion
import Universality.Percolation.GenerationMassCharacteristic

namespace Universality.FiniteNetwork
noncomputable section

theorem conditional_mass_probability_eq_of_characteristic_eq {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ)
    (firstOpened firstSource firstTarget secondOpened secondSource secondTarget : Bool)
    (hcharacteristic : ∀ t : ℝ,
      R.conditionalInternalCharacteristic p firstOpened firstSource firstTarget t =
        R.conditionalInternalCharacteristic p secondOpened secondSource secondTarget t)
    (size : ℕ) :
    R.conditionalInternalMassProbability p firstOpened firstSource firstTarget size =
      R.conditionalInternalMassProbability p secondOpened secondSource secondTarget size := by
  have hfirst := R.conditionalInternalCharacteristic_scaled_inversion p firstOpened firstSource firstTarget size 1 zero_lt_one
  have hsecond := R.conditionalInternalCharacteristic_scaled_inversion p secondOpened secondSource secondTarget size 1 zero_lt_one
  simp only [Complex.ofReal_one, one_mul] at hfirst hsecond
  simp_rw [hcharacteristic] at hfirst
  have heq := hfirst.symm.trans hsecond
  have hnonzero : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact Complex.ofReal_inj.mp ((mul_left_cancel₀ hnonzero) heq)

theorem child_conditional_mass_probability {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (state child : LiveState) (coarse : Configuration outerEdges) (edge : Fin outerEdges)
    (hchild : R.childState state coarse edge = some child) (size : ℕ) :
    S.conditionalInternalMassProbability p (coarse edge)
      (R.orientedChildState true (state == .both) coarse edge).sourceSelected
      (R.orientedChildState true (state == .both) coarse edge).targetSelected size =
    S.conditionalInternalMassProbability p (child == .connected) true (child == .both) size := by
  apply S.conditional_mass_probability_eq_of_characteristic_eq
  intro t
  have h := R.child_conditionalVertexCharacteristic S symmetry hs ht p hpositive hless state coarse edge t
  simpa only [hchild, conditionalVertexCharacteristic] using h

end
end Universality.FiniteNetwork

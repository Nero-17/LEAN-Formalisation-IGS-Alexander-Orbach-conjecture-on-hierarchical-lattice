import Universality.Percolation.InternalMassSymmetry
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Exact characteristic function of the conditional internal mass. -/
def conditionalInternalCharacteristic (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (t : ℝ) : ℂ :=
  ∑ ω, (R.conditionalCellWeight p opened ω : ℂ) *
    Complex.exp ((t * R.internalSelectedMass sourceSelected targetSelected ω : ℝ) * Complex.I)

theorem conditionalInternalCharacteristic_zero (R : FiniteNetwork vertices edges) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) :
    R.conditionalInternalCharacteristic p opened sourceSelected targetSelected 0 = 1 := by
  simp only [conditionalInternalCharacteristic, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one, ← Complex.ofReal_sum]
  rw [R.sum_conditionalCellWeight p hpositive hless, Complex.ofReal_one]

theorem conditionalInternalCharacteristic_inactive (R : FiniteNetwork vertices edges) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened : Bool) (t : ℝ) :
    R.conditionalInternalCharacteristic p opened false false t = 1 := by
  simp only [conditionalInternalCharacteristic, internalSelectedMass, selectedActive,
    Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Finset.sum_const_zero, Nat.cast_zero, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_sum]
  rw [R.sum_conditionalCellWeight p hpositive hless, Complex.ofReal_one]

theorem NetworkSymmetry.conditionalInternalCharacteristic_swap {R : FiniteNetwork vertices edges}
    (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) (t : ℝ) :
    R.conditionalInternalCharacteristic p opened sourceSelected targetSelected t =
      R.conditionalInternalCharacteristic p opened targetSelected sourceSelected t := by
  unfold conditionalInternalCharacteristic
  rw [← symmetry.configurationEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  rw [symmetry.conditionalCellWeight R hs ht,
    symmetry.internalSelectedMass_configuration hs ht]

theorem conditionalInternalCharacteristic_connected (R : FiniteNetwork vertices edges) (p t : ℝ) :
    R.conditionalInternalCharacteristic p true true true t =
      R.conditionalInternalCharacteristic p true true false t := by
  unfold conditionalInternalCharacteristic
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hcross : R.crosses ω = true
  · rw [R.internalSelectedMass_connected ω hcross]
  · simp [conditionalCellWeight, hcross]

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- The real conditional disintegration also applies to arbitrary complex observables. -/
theorem conditional_substitution_complex_observable
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened : Bool)
    (response : Configuration outerEdges → (Fin outerEdges → Configuration innerEdges) → ℂ) :
    (∑ cells, ((R.substitute S).conditionalCellWeight p opened
        (substitutionConfigurationEquiv cells) : ℂ) * response (S.coarseConfiguration cells) cells) =
      ∑ coarse, (R.conditionalCellWeight (S.reliability p) opened coarse : ℂ) *
        ∑ cells, (∏ e, (S.conditionalCellWeight p (coarse e) (cells e) : ℂ)) * response coarse cells := by
  apply Complex.ext
  · simpa only [← Complex.ofReal_prod, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      R.conditional_substitution_observable S p hpositive hless opened
        (fun coarse cells => (response coarse cells).re)
  · simpa only [← Complex.ofReal_prod, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      R.conditional_substitution_observable S p hpositive hless opened
        (fun coarse cells => (response coarse cells).im)

/-- Exact Fourier recursion including the dependent coarse reward and child types. -/
theorem conditionalInternalCharacteristic_substitute (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) (t : ℝ) :
    (R.substitute S).conditionalInternalCharacteristic p opened sourceSelected targetSelected t =
      ∑ coarse, (R.conditionalCellWeight (S.reliability p) opened coarse : ℂ) *
        Complex.exp ((t * R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) * Complex.I) *
          ∏ e, S.conditionalInternalCharacteristic p (coarse e)
            (R.orientedChildState sourceSelected targetSelected coarse e).sourceSelected
            (R.orientedChildState sourceSelected targetSelected coarse e).targetSelected t := by
  unfold conditionalInternalCharacteristic
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.internalSelectedMass_substitute S, Nat.cast_add]
  rw [R.conditional_substitution_complex_observable S p hpositive hless opened
    (fun coarse cells => Complex.exp ((t *
      (R.internalSelectedMass sourceSelected targetSelected coarse +
        ∑ e, S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) (cells e)) : ℝ) * Complex.I))]
  apply Finset.sum_congr rfl
  intro coarse _
  rw [mul_assoc]
  congr 1
  have hexp (cells : Fin outerEdges → Configuration innerEdges) :
      Complex.exp ((t *
        (R.internalSelectedMass sourceSelected targetSelected coarse +
          ∑ e, S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) (cells e)) : ℝ) * Complex.I) =
      Complex.exp ((t * R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) * Complex.I) *
        ∏ e, Complex.exp ((t * S.internalStateMass
          (R.orientedChildState sourceSelected targetSelected coarse e) (cells e) : ℝ) * Complex.I) := by
    simp only [Nat.cast_add, Nat.cast_sum, mul_add, Complex.ofReal_add, add_mul,
      Complex.exp_add, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [hexp]
  have hfactor (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ e, (S.conditionalCellWeight p (coarse e) (cells e) : ℂ)) *
        (Complex.exp ((t * R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) * Complex.I) *
          ∏ e, Complex.exp ((t * S.internalStateMass
            (R.orientedChildState sourceSelected targetSelected coarse e) (cells e) : ℝ) * Complex.I)) =
      Complex.exp ((t * R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) * Complex.I) *
        ∏ e, (S.conditionalCellWeight p (coarse e) (cells e) : ℂ) *
          Complex.exp ((t * S.internalStateMass
            (R.orientedChildState sourceSelected targetSelected coarse e) (cells e) : ℝ) * Complex.I) := by
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [internalStateMass] using (Fintype.prod_sum
    (fun e cell => (S.conditionalCellWeight p (coarse e) cell : ℂ) *
      Complex.exp ((t * S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) cell : ℝ) * Complex.I))).symm

end
end Universality.FiniteNetwork


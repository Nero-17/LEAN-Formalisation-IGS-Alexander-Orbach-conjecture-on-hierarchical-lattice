import Universality.Percolation.CharacteristicContraction
import Universality.Probability.CharacteristicRigidity

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

/-- Two consecutive positive-probability atoms exclude unit Fourier modulus
away from the ordinary integer-lattice period. -/
theorem conditional_mass_norm_lt_one_of_zero_one (R : FiniteNetwork vertices edges)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened sourceSelected targetSelected : Bool)
    (first second : Configuration edges)
    (hfirst : 0 < R.conditionalCellWeight p opened first)
    (hsecond : 0 < R.conditionalCellWeight p opened second)
    (hmassFirst : R.internalSelectedMass sourceSelected targetSelected first = 0)
    (hmassSecond : R.internalSelectedMass sourceSelected targetSelected second = 1)
    (t : ℝ) (ht : Complex.exp ((t : ℂ) * Complex.I) ≠ 1) :
    ‖R.conditionalInternalCharacteristic p opened sourceSelected targetSelected t‖ < 1 := by
  by_contra hnot
  have hunit : ‖R.conditionalInternalCharacteristic p opened sourceSelected targetSelected t‖ = 1 :=
    le_antisymm (R.norm_conditionalInternalCharacteristic_le_one p hp hp' hpositive hless _ _ _ _)
      (le_of_not_gt hnot)
  have hphase (configuration : Configuration edges)
      (hconfiguration : 0 < R.conditionalCellWeight p opened configuration) :=
    weighted_characteristic_eq_unit
      (R.conditionalCellWeight p opened)
      (fun cell => Complex.exp ((t * R.internalSelectedMass sourceSelected targetSelected cell : ℝ) * Complex.I))
      (R.conditionalInternalCharacteristic p opened sourceSelected targetSelected t)
      (fun _ => R.conditionalCellWeight_nonneg hp hp' _ _)
      (R.sum_conditionalCellWeight p hpositive hless opened)
      (fun _ => (Complex.norm_exp_ofReal_mul_I _).le) hunit rfl configuration hconfiguration
  have hzero := hphase first hfirst
  have hone := hphase second hsecond
  simp only [hmassFirst, Nat.cast_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hzero
  simp only [hmassSecond, Nat.cast_one, mul_one] at hone
  exact ht (hone.trans hzero.symm)

end
end Universality.FiniteNetwork

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-- A continuous expectation solving the eigenfunction integral equation
has the exact exponential evolution. The differential equation and its
integrating factor are derived, rather than supplied as assumptions. -/
theorem eigen_expectation_integral_equation_completion20261011
    (expectation : ℝ → ℝ) (eigenvalue : ℝ)
    (continuous : ContinuousOn expectation (Ici 0))
    (integralEquation : ∀ time, 0 ≤ time →
      expectation time = expectation 0 - eigenvalue * ∫ other in 0..time, expectation other) :
    ∀ time, 0 ≤ time → expectation time = Real.exp (-eigenvalue * time) * expectation 0 := by
  have rightDerivative (time : ℝ) (nonnegative : 0 ≤ time) :
      HasDerivWithinAt expectation (-eigenvalue * expectation time) (Ici time) time := by
    have continuousRight : ContinuousOn expectation (Ici time) :=
      continuous.mono (Ici_subset_Ici.mpr nonnegative)
    have integrable : IntervalIntegrable expectation volume 0 time :=
      (continuous.mono (show Icc 0 time ⊆ Ici 0 by intro point member; exact member.1)).intervalIntegrable_of_Icc nonnegative
    have continuousOpenRight : ContinuousOn expectation (Ioi time) :=
      continuousRight.mono Ioi_subset_Ici_self
    have primitiveDerivative := intervalIntegral.integral_hasDerivWithinAt_right
      (s := Ici time) (t := Ioi time) integrable
      (continuousOpenRight.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi time)
      ((continuousRight time (by simp)).mono Ioi_subset_Ici_self)
    have formulaDerivative := (hasDerivAt_const time (expectation 0)).hasDerivWithinAt.sub
      (primitiveDerivative.const_mul eigenvalue)
    have agrees : ∀ point ∈ Ici time, expectation point =
        expectation 0 - eigenvalue * ∫ other in 0..point, expectation other :=
      fun point member => integralEquation point (nonnegative.trans member)
    exact (formulaDerivative.congr_of_mem agrees (by simp)).congr_deriv (by ring)
  let weighted := fun time => Real.exp (eigenvalue * time) * expectation time
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (eigenvalue * time)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have weightedContinuous : ContinuousOn weighted (Ici 0) :=
    exponentialContinuous.continuousOn.mul continuous
  have weightedDerivative (time : ℝ) (nonnegative : 0 ≤ time) :
      HasDerivWithinAt weighted 0 (Ici time) time := by
    have exponentialDerivative : HasDerivWithinAt (fun point => Real.exp (eigenvalue * point))
        (Real.exp (eigenvalue * time) * eigenvalue) (Ici time) time := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id time).const_mul eigenvalue).exp).hasDerivWithinAt
    dsimp only [weighted]
    exact (exponentialDerivative.mul (rightDerivative time nonnegative)).congr_deriv (by ring)
  intro time nonnegative
  have constant := constant_of_has_deriv_right_zero
    (weightedContinuous.mono (show Icc 0 time ⊆ Ici 0 by intro point member; exact member.1))
    (fun point member => weightedDerivative point member.1)
  have weightedEquality := constant time ⟨nonnegative, le_rfl⟩
  dsimp only [weighted] at weightedEquality
  simp only [mul_zero, Real.exp_zero, one_mul] at weightedEquality
  have cancellation : Real.exp (-eigenvalue * time) * Real.exp (eigenvalue * time) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  calc
    expectation time = 1 * expectation time := (one_mul _).symm
    _ = (Real.exp (-eigenvalue * time) * Real.exp (eigenvalue * time)) * expectation time := by rw [cancellation]
    _ = Real.exp (-eigenvalue * time) * (Real.exp (eigenvalue * time) * expectation time) := mul_assoc _ _ _
    _ = Real.exp (-eigenvalue * time) * expectation 0 := by rw [weightedEquality]

end
end IGSIII34.Diffusion

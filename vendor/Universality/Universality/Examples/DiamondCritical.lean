import Universality.Examples.Diamond
import Universality.Matrix.TwoByTwoExpansion

namespace Universality
noncomputable section
open FiniteNetwork Matrix Polynomial

def diamondCriticalProbability : ℝ := (Real.sqrt 5 - 1) / 2

theorem diamond_critical_probability_bounds :
    0 < diamondCriticalProbability ∧ diamondCriticalProbability < 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [diamondCriticalProbability]
  constructor <;> nlinarith

theorem diamond_critical_quadratic :
    diamondCriticalProbability ^ 2 + diamondCriticalProbability - 1 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [diamondCriticalProbability]
  nlinarith

theorem diamond_critical_fixed_point :
    diamondNetwork.reliability diamondCriticalProbability = diamondCriticalProbability := by
  rw [diamond_reliability]
  apply sub_eq_zero.mp
  have hfactor (p : ℝ) : 2 * p ^ 2 - p ^ 4 - p = -p * (p - 1) * (p ^ 2 + p - 1) := by ring
  rw [hfactor, diamond_critical_quadratic, mul_zero]

theorem diamond_reliability_derivative (p : ℝ) :
    deriv diamondNetwork.reliability p = 4 * p * (1 - p ^ 2) := by
  rw [(diamondNetwork.hasDerivAt_reliability p).deriv, diamond_reliabilityPolynomial]
  norm_num [Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_X_pow]
  ring

theorem diamond_critical_response :
    deriv diamondNetwork.reliability diamondCriticalProbability = 6 - 2 * Real.sqrt 5 := by
  rw [diamond_reliability_derivative]
  have h := diamond_critical_quadratic
  have hmul := congrArg (fun x : ℝ => x * diamondCriticalProbability) h
  have hp : 2 * diamondCriticalProbability = Real.sqrt 5 - 1 := by
    dsimp [diamondCriticalProbability]
    ring
  nlinarith

theorem diamond_critical_block :
    massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability) =
      !![8 * diamondCriticalProbability ^ 2, 4 * diamondCriticalProbability ^ 2;
        2 * diamondCriticalProbability ^ 2, 2] := by
  obtain ⟨hp, hp'⟩ := diamond_critical_probability_bounds
  rw [diamond_massMatrix _ hp hp']
  have h := diamond_critical_quadratic
  have hmul := congrArg (fun x : ℝ => x * diamondCriticalProbability) h
  have hmul₂ := congrArg (fun x : ℝ => x * diamondCriticalProbability ^ 2) h
  have hplus : 1 + diamondCriticalProbability ≠ 0 := by linarith
  have htwo : 2 - diamondCriticalProbability ^ 2 ≠ 0 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [massPlaneBlock, diamondMassFormula] <;>
    field_simp [hplus, htwo] <;> nlinarith

theorem diamond_critical_block_trace :
    Matrix.trace (massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability)) =
      14 - 4 * Real.sqrt 5 := by
  rw [diamond_critical_block, Matrix.trace_fin_two]
  norm_num
  have h := diamond_critical_quadratic
  have hp : 2 * diamondCriticalProbability = Real.sqrt 5 - 1 := by
    dsimp [diamondCriticalProbability]
    ring
  nlinarith

theorem diamond_critical_block_det :
    Matrix.det (massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability)) =
      4 * (Real.sqrt 5 - 1) := by
  rw [diamond_critical_block, Matrix.det_fin_two]
  norm_num
  have h := diamond_critical_quadratic
  have hmul := congrArg (fun x : ℝ => x * diamondCriticalProbability) h
  have hmul₂ := congrArg (fun x : ℝ => x * diamondCriticalProbability ^ 2) h
  have hp : 2 * diamondCriticalProbability = Real.sqrt 5 - 1 := by
    dsimp [diamondCriticalProbability]
    ring
  nlinarith

end
end Universality

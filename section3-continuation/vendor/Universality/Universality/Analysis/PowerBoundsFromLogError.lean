import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace Universality
noncomputable section

/-- A bounded logarithmic error implies genuine two-constant power bounds. -/
theorem rpow_bounds_of_log_error (response size exponent bound : ℝ)
    (hresponse : 0 < response) (hsize : 0 < size)
    (herror : |Real.log response - exponent * Real.log size| ≤ bound) :
    Real.exp (-bound) * size ^ exponent ≤ response ∧
      response ≤ Real.exp bound * size ^ exponent := by
  obtain ⟨hlower, hupper⟩ := abs_le.mp herror
  constructor
  · calc
      _ = Real.exp (-bound + Real.log size * exponent) := by
        rw [Real.rpow_def_of_pos hsize, Real.exp_add]
      _ ≤ Real.exp (Real.log response) := Real.exp_le_exp.mpr (by nlinarith only [hlower])
      _ = response := Real.exp_log hresponse
  · calc
      response = Real.exp (Real.log response) := (Real.exp_log hresponse).symm
      _ ≤ Real.exp (bound + Real.log size * exponent) := Real.exp_le_exp.mpr (by nlinarith only [hupper])
      _ = _ := by rw [Real.rpow_def_of_pos hsize, Real.exp_add]

end
end Universality

import IGSIII34.Spectral.ContinuousKernelProbabilityCompletion20261011
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped _root_.Topology ENNReal
variable {Space : Type*} [MeasurableSpace Space]

def scalarSpeedMeasureCompletion20261011 (measure : Measure Space) (constant : ℝ) : Measure Space :=
  ENNReal.ofReal constant • measure

theorem scalarSpeedMeasure_density_identity_completion20261011
    (measure : Measure Space) (constant : ℝ) (positive : 0 < constant) (kernel : Space → ℝ) :
    (scalarSpeedMeasureCompletion20261011 measure constant).withDensity
      (fun point => ENNReal.ofReal (constant⁻¹ * kernel point)) =
      measure.withDensity (fun point => ENNReal.ofReal (kernel point)) := by
  unfold scalarSpeedMeasureCompletion20261011
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr positive.le)]
  rw [withDensity_smul_measure]
  change ENNReal.ofReal constant • measure.withDensity
    (ENNReal.ofReal constant⁻¹ • fun point => ENNReal.ofReal (kernel point)) = _
  rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul,
    ← ENNReal.ofReal_mul positive.le, mul_inv_cancel₀ positive.ne', ENNReal.ofReal_one, one_smul]

theorem scalarSpeedMeasure_integral_completion20261011
    (measure : Measure Space) (constant : ℝ) (nonnegative : 0 ≤ constant) (function : Space → ℝ) :
    (∫ point, function point ∂scalarSpeedMeasureCompletion20261011 measure constant) =
      constant * ∫ point, function point ∂measure := by
  rw [scalarSpeedMeasureCompletion20261011, integral_smul_measure, ENNReal.toReal_ofReal nonnegative, smul_eq_mul]

theorem scalarSpeedMeasure_kernel_integral_completion20261011
    (measure : Measure Space) (constant : ℝ) (positive : 0 < constant)
    (kernel function : Space → ℝ) :
    (∫ point, (constant⁻¹ * kernel point) * function point
      ∂scalarSpeedMeasureCompletion20261011 measure constant) =
      ∫ point, kernel point * function point ∂measure := by
  rw [scalarSpeedMeasure_integral_completion20261011 measure constant positive.le]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simp only [← mul_assoc, mul_inv_cancel₀ positive.ne', one_mul]

theorem scalarSpeedMeasure_variational_equivalence_completion20261011
    (measure : Measure Space) (constant : ℝ) (positive : 0 < constant)
    (energy parameter : ℝ) (potential test forcing : Space → ℝ) :
    (energy + parameter * ∫ point, potential point * test point
      ∂scalarSpeedMeasureCompletion20261011 measure constant =
        ∫ point, forcing point * test point ∂scalarSpeedMeasureCompletion20261011 measure constant) ↔
    (energy + (parameter * constant) * ∫ point, potential point * test point ∂measure =
        constant * ∫ point, forcing point * test point ∂measure) := by
  rw [scalarSpeedMeasure_integral_completion20261011 measure constant positive.le,
    scalarSpeedMeasure_integral_completion20261011 measure constant positive.le, mul_assoc]

section Kernel
variable [TopologicalSpace Space] [CompactSpace Space] [T2Space Space]
  [SecondCountableTopology Space] [BorelSpace Space]
  (measure : Measure Space) [IsProbabilityMeasure measure]

/-- A density with respect to C times the speed measure uses 1/C times
the original kernel. The resulting transition measure is exactly the
original one at the selected time. -/
local instance scalarSpeedMeasureFiniteCompletion20261011 (constant : ℝ) :
    IsFiniteMeasure (scalarSpeedMeasureCompletion20261011 measure constant) := by
  unfold scalarSpeedMeasureCompletion20261011
  constructor
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.ofReal_lt_top

def scalarSpeedTransitionKernelCompletion20261011 (constant : ℝ) (kernel : C(Space × Space, ℝ)) : Kernel Space Space :=
  (Kernel.const Space (scalarSpeedMeasureCompletion20261011 measure constant)).withDensity
    (fun first second => ENNReal.ofReal (constant⁻¹ * kernel (first, second)))

theorem scalarSpeedTransitionKernel_identity_completion20261011
    (constant : ℝ) (positive : 0 < constant) (kernel : C(Space × Space, ℝ)) :
    scalarSpeedTransitionKernelCompletion20261011 measure constant kernel =
      continuousTransitionKernelCompletion20261011 measure kernel := by
  ext first : 1
  rw [scalarSpeedTransitionKernelCompletion20261011, Kernel.withDensity_apply]
  · rw [continuousTransitionKernel_apply_completion20261011]
    exact scalarSpeedMeasure_density_identity_completion20261011 measure constant positive _
  · exact ENNReal.measurable_ofReal.comp ((continuous_const.mul kernel.continuous).measurable)

theorem scalarSpeedTransitionKernel_isMarkov_completion20261011
    (constant : ℝ) (positive : 0 < constant) (kernel : C(Space × Space, ℝ))
    (nonnegative : ∀ first second, 0 ≤ kernel (first, second))
    (rows : ∀ first, ∫ second, kernel (first, second) ∂measure = 1) :
    IsMarkovKernel (scalarSpeedTransitionKernelCompletion20261011 measure constant kernel) := by
  rw [scalarSpeedTransitionKernel_identity_completion20261011 measure constant positive kernel]
  exact continuousTransitionKernel_isMarkov_completion20261011 measure kernel nonnegative rows

end Kernel
end
end IGSIII34.Spectral

import Mathlib.Topology.CompactOpen
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory InnerProductSpace
open scoped Topology

variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space] [T2Space Space]
  [MeasurableSpace Space] [BorelSpace Space] (measure : Measure Space) [IsProbabilityMeasure measure]

def continuousKernelRowsCompletion (kernel : C(Space × Space, ℝ)) : C(Space, Lp ℝ 2 measure) :=
  ⟨fun point => ContinuousMap.toLp 2 measure ℝ (kernel.curry point),
    (ContinuousMap.toLp 2 measure ℝ).continuous.comp kernel.curry.continuous⟩

def continuousKernelValueCompletion (kernel : C(Space × Space, ℝ))
    (forcing : Lp ℝ 2 measure) : C(Space, ℝ) :=
  ⟨fun point => inner ℝ (continuousKernelRowsCompletion measure kernel point) forcing,
    (continuousKernelRowsCompletion measure kernel).continuous.inner continuous_const⟩

theorem continuousKernelValue_norm_le_completion (kernel : C(Space × Space, ℝ))
    (forcing : Lp ℝ 2 measure) :
    ‖continuousKernelValueCompletion measure kernel forcing‖ ≤
      ‖continuousKernelRowsCompletion measure kernel‖ * ‖forcing‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro point
  exact (norm_inner_le_norm (continuousKernelRowsCompletion measure kernel point) forcing).trans
    (mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm _ point) (norm_nonneg forcing))

def continuousKernelL2OperatorCompletion (kernel : C(Space × Space, ℝ)) :
    Lp ℝ 2 measure →L[ℝ] C(Space, ℝ) :=
  (show Lp ℝ 2 measure →ₗ[ℝ] C(Space, ℝ) from
    { toFun := continuousKernelValueCompletion measure kernel
      map_add' := by
        intro first second
        ext point
        change inner ℝ (continuousKernelRowsCompletion measure kernel point) (first + second) =
          inner ℝ (continuousKernelRowsCompletion measure kernel point) first +
          inner ℝ (continuousKernelRowsCompletion measure kernel point) second
        exact inner_add_right _ _ _
      map_smul' := by
        intro scalar forcing
        ext point
        change inner ℝ (continuousKernelRowsCompletion measure kernel point) (scalar • forcing) =
          scalar * inner ℝ (continuousKernelRowsCompletion measure kernel point) forcing
        exact real_inner_smul_right _ _ _ }).mkContinuous
          ‖continuousKernelRowsCompletion measure kernel‖
          (continuousKernelValue_norm_le_completion measure kernel)

theorem continuousKernelL2Operator_integral_completion (kernel : C(Space × Space, ℝ))
    (forcing : Lp ℝ 2 measure) (point : Space) :
    continuousKernelL2OperatorCompletion measure kernel forcing point =
      ∫ other, kernel (point, other) * forcing other ∂measure := by
  change inner ℝ (ContinuousMap.toLp 2 measure ℝ (kernel.curry point)) forcing = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have representative := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure (kernel.curry point)
  filter_upwards [representative] with other equality
  rw [equality]
  simp [mul_comm]

end
end IGSIII34.Spectral

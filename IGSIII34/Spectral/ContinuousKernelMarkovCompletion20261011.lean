import IGSIII34.Spectral.ContinuousKernelOperatorCompletion20261011
import IGSIII34.Spectral.ContinuousLpOrderCompletion20261011

/-! Positivity and row mass of a continuous kernel follow from the proved
order and constant properties of its L² integral operator. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped Topology

variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space] [T2Space Space]
  [MeasurableSpace Space] [BorelSpace Space] (measure : Measure Space)
  [IsProbabilityMeasure measure] [measure.IsOpenPosMeasure]

theorem continuous_kernel_pointwise_nonnegative_completion20261011
    (kernel : C(Space × Space, ℝ))
    (positive : ∀ forcing : Lp ℝ 2 measure, 0 ≤ forcing →
      0 ≤ ContinuousMap.toLp 2 measure ℝ (continuousKernelL2OperatorCompletion20261011 measure kernel forcing))
    (point other : Space) : 0 ≤ kernel (point, other) := by
  let test : C(Space, ℝ) :=
    ⟨fun vertex => max (-kernel (point, vertex)) 0,
      ((kernel.continuous.comp (continuous_const.prodMk continuous_id)).neg.max continuous_const)⟩
  let testL2 := ContinuousMap.toLp 2 measure ℝ test
  have testNonnegative : 0 ≤ testL2 := by
    have order := (continuousMap_le_iff_toLp_le_completion20261011 measure (0 : C(Space, ℝ)) test).mp
      (fun vertex => le_max_right _ _)
    simpa only [map_zero] using order
  have valueNonnegative := continuousMap_nonnegative_of_toLp_nonnegative_completion20261011 measure
    (continuousKernelL2OperatorCompletion20261011 measure kernel testL2) (positive testL2 testNonnegative) point
  have negativeSquare : continuousKernelL2OperatorCompletion20261011 measure kernel testL2 point = -‖testL2‖ ^ 2 := by
    change inner ℝ (ContinuousMap.toLp 2 measure ℝ (kernel.curry point)) testL2 = -‖testL2‖ ^ 2
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure (kernel.curry point), ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure test]
      with vertex rowAt testAt
    rw [rowAt, testAt]
    simp only [Real.inner_apply]
    change kernel (point, vertex) * max (-kernel (point, vertex)) 0 =
      -(max (-kernel (point, vertex)) 0 * max (-kernel (point, vertex)) 0)
    by_cases nonnegative : 0 ≤ kernel (point, vertex)
    · rw [max_eq_right (neg_nonpos.mpr nonnegative)]; simp
    · rw [max_eq_left (by linarith : 0 ≤ -kernel (point, vertex))]; ring
  have normZero : ‖testL2‖ = 0 := by nlinarith [norm_nonneg testL2]
  have testZero : test = 0 := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure
    simpa only [map_zero] using norm_eq_zero.mp normZero
  have testAtZero := congrArg (fun function : C(Space, ℝ) => function other) testZero
  change max (-kernel (point, other)) 0 = 0 at testAtZero
  have bound := le_max_left (-kernel (point, other)) 0
  rw [testAtZero] at bound
  linarith

theorem continuous_kernel_row_integral_one_completion20261011
    (kernel : C(Space × Space, ℝ))
    (conservative : ContinuousMap.toLp 2 measure ℝ
      (continuousKernelL2OperatorCompletion20261011 measure kernel
        (ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space (1 : ℝ)))) =
      ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space (1 : ℝ)))
    (point : Space) : ∫ other, kernel (point, other) ∂measure = 1 := by
  have same : continuousKernelL2OperatorCompletion20261011 measure kernel
      (ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space (1 : ℝ))) = ContinuousMap.const Space (1 : ℝ) :=
    ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure conservative
  have pointValue := congrArg (fun function : C(Space, ℝ) => function point) same
  rw [continuousKernelL2Operator_integral_completion20261011] at pointValue
  have integralSame : (∫ other, kernel (point, other) *
      (ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const Space (1 : ℝ))) other ∂measure) =
      ∫ other, kernel (point, other) ∂measure := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure (ContinuousMap.const Space (1 : ℝ))] with other equality
    rw [equality]
    simp
  rw [integralSame] at pointValue
  exact pointValue

end
end IGSIII34.Spectral




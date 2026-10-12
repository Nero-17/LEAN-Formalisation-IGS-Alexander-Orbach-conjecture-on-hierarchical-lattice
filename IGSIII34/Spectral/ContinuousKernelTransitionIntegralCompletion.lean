import IGSIII34.Spectral.ContinuousKernelProbabilityCompletion

set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

variable {Space : Type*} [TopologicalSpace Space] [CompactSpace Space] [T2Space Space]
  [SecondCountableTopology Space] [MeasurableSpace Space] [BorelSpace Space]
  (measure : Measure Space) [IsProbabilityMeasure measure]

theorem continuousTransitionKernel_integral_completion
    (kernel : C(Space × Space, ℝ)) (nonnegative : ∀ first second, 0 ≤ kernel (first, second))
    (function : Space → ℝ) (point : Space) :
    (∫ other, function other ∂continuousTransitionKernelCompletion measure kernel point) =
      ∫ other, kernel (point, other) * function other ∂measure := by
  rw [continuousTransitionKernel_apply_completion]
  change (∫ other, function other ∂measure.withDensity
    (fun other => ((Real.toNNReal (kernel (point, other)) : ℝ≥0) : ℝ≥0∞))) = _
  have measurableDensity : Measurable (fun other : Space => Real.toNNReal (kernel (point, other))) := by
    exact (continuous_real_toNNReal.comp (kernel.continuous.comp (continuous_const.prodMk continuous_id))).measurable
  rw [integral_withDensity_eq_integral_smul measurableDensity]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro other
  change (Real.toNNReal (kernel (point, other)) : ℝ) * function other = _
  rw [Real.coe_toNNReal _ (nonnegative point other)]

theorem continuousTransitionKernel_continuous_expectation_completion
    (kernel : C(Space × Space, ℝ)) (nonnegative : ∀ first second, 0 ≤ kernel (first, second))
    (function : C(Space, ℝ)) (point : Space) :
    (∫ other, function other ∂continuousTransitionKernelCompletion measure kernel point) =
      continuousKernelL2OperatorCompletion measure kernel (ContinuousMap.toLp 2 measure ℝ function) point := by
  rw [continuousTransitionKernel_integral_completion measure kernel nonnegative,
    continuousKernelL2Operator_integral_completion]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure function] with other equality
  rw [equality]

end
end IGSIII34.Spectral

import IGSIII34.Diffusion.AeFiniteStoppingFellerMarkovCompletion
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped _root_.Topology NNReal
variable {Omega Space : Type*} [ambient : MeasurableSpace Omega]
  [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem restricted_transition_law_eq_of_continuous_condExp_completion
    (measure : Measure Omega) [IsFiniteMeasure measure]
    (known : MeasurableSpace Omega) (knownBelow : known ≤ ambient)
    (current future : Omega → Space) (currentMeasurable : Measurable[ambient] current) (futureMeasurable : Measurable[ambient] future)
    (kernel : Kernel Space Space) [IsMarkovKernel kernel]
    (transform : C(Space, ℝ) → C(Space, ℝ))
    (expectation : ∀ function : C(Space, ℝ), ∀ point, (∫ other, function other ∂kernel point) = transform function point)
    (conditional : ∀ function : C(Space, ℝ),
      measure[(fun sample => function (future sample)) | known] =ᵐ[measure]
        fun sample => transform function (current sample))
    (event : Set Omega) (eventKnown : MeasurableSet[known] event) :
    letI : MeasurableSpace Omega := ambient
    (measure.restrict event).map future = kernel ∘ₘ ((measure.restrict event).map current) := by
  letI : MeasurableSpace Omega := ambient
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro function
  have futureIntegrable : Integrable (fun sample => function (future sample)) measure :=
    Integrable.of_bound (function.continuous.measurable.comp futureMeasurable).aestronglyMeasurable ‖function‖
      (ae_of_all _ fun sample => function.norm_coe_le_norm _)
  have kernelIntegral : (∫ point, function point ∂(kernel ∘ₘ ((measure.restrict event).map current))) =
      ∫ point, transform function.toContinuousMap point ∂(measure.restrict event).map current := by
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (function.integrable _)]
    simp only [Kernel.const_apply]
    exact integral_congr_ae (ae_of_all _ fun point => expectation function.toContinuousMap point)
  calc
    (∫ point, function point ∂(measure.restrict event).map future) =
        ∫ sample in event, function (future sample) ∂measure :=
      integral_map futureMeasurable.aemeasurable function.continuous.measurable.aestronglyMeasurable
    _ = ∫ sample in event, (measure[(fun sample => function (future sample)) | known]) sample ∂measure :=
      (setIntegral_condExp knownBelow futureIntegrable eventKnown).symm
    _ = ∫ sample in event, transform function.toContinuousMap (current sample) ∂measure :=
      setIntegral_congr_ae (knownBelow _ eventKnown) ((conditional function.toContinuousMap).mono fun sample equality _ => equality)
    _ = ∫ point, transform function.toContinuousMap point ∂(measure.restrict event).map current :=
      (integral_map currentMeasurable.aemeasurable (transform function.toContinuousMap).continuous.measurable.aestronglyMeasurable).symm
    _ = _ := kernelIntegral.symm

end
end IGSIII34.Diffusion


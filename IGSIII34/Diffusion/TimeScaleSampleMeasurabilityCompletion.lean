import IGSIII34.Diffusion.GlobalTimeRescaleWeakCompletion
import IGSIII34.Diffusion.ActualHoldingSkorokhodMeasurabilityCompletion

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal
variable {Space Vertex : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]

theorem timeScale_holding_sample_identity_completion
    (ratio : ℝ≥0) (acceleration : ℝ) (placement : Vertex → Space)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) :
    skorokhodGlobalTimeScaleCompletion ratio
      (holdingGlobalSkorokhodSampleCompletion acceleration placement sample) =
    holdingGlobalSkorokhodSampleCompletion (acceleration*(ratio:ℝ)) placement sample := by
  apply congrArg SkorokhodGlobalPathCompletion.mk
  funext time
  change placement (holdingTimePath sample.1 sample.2 (acceleration*((ratio*time:ℝ≥0):ℝ))) =
    placement (holdingTimePath sample.1 sample.2 ((acceleration*(ratio:ℝ))*(time:ℝ)))
  rw [NNReal.coe_mul, mul_assoc]

theorem timeScale_discrete_sample_identity_completion
    (ratio : ℝ≥0) (acceleration : ℝ) (placement : Vertex → Space) (trajectory : ℕ → Vertex) :
    skorokhodGlobalTimeScaleCompletion ratio
      (discreteGlobalSkorokhodSampleCompletion acceleration placement trajectory) =
    discreteGlobalSkorokhodSampleCompletion (acceleration*(ratio:ℝ)) placement trajectory := by
  apply congrArg SkorokhodGlobalPathCompletion.mk
  funext time
  change placement (trajectory ⌊acceleration*((ratio*time:ℝ≥0):ℝ)⌋₊) =
    placement (trajectory ⌊(acceleration*(ratio:ℝ))*(time:ℝ)⌋₊)
  rw [NNReal.coe_mul, mul_assoc]

theorem timeScale_holding_sample_aemeasurable_completion
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (ratio : ℝ≥0) (ratioPositive : 0 < ratio)
    (acceleration : ℝ) (accelerationPositive : 0 < acceleration) (placement : Vertex → Space) :
    AEMeasurable (fun sample => skorokhodGlobalTimeScaleCompletion ratio
      (holdingGlobalSkorokhodSampleCompletion acceleration placement sample)) law := by
  simpa only [timeScale_holding_sample_identity_completion] using
    holdingGlobalSkorokhodSample_aemeasurable_completion law regular (acceleration*(ratio:ℝ))
      (mul_pos accelerationPositive (NNReal.coe_pos.mpr ratioPositive)) placement

theorem timeScale_discrete_sample_measurable_completion
    (ratio : ℝ≥0) (acceleration : ℝ) (accelerationNonnegative : 0 ≤ acceleration) (placement : Vertex → Space) :
    Measurable (fun trajectory => skorokhodGlobalTimeScaleCompletion ratio
      (discreteGlobalSkorokhodSampleCompletion acceleration placement trajectory)) := by
  simpa only [timeScale_discrete_sample_identity_completion] using
    discreteGlobalSkorokhodSample_measurable_completion (acceleration*(ratio:ℝ))
      (mul_nonneg accelerationNonnegative ratio.property) placement

end
end IGSIII34.Diffusion

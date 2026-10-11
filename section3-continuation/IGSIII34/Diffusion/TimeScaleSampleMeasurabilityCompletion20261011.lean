import IGSIII34.Diffusion.GlobalTimeRescaleWeakCompletion20261011
import IGSIII34.Diffusion.ActualHoldingSkorokhodMeasurabilityCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal
variable {Space Vertex : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]

theorem timeScale_holding_sample_identity_completion20261011
    (ratio : ℝ≥0) (acceleration : ℝ) (placement : Vertex → Space)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) :
    skorokhodGlobalTimeScaleCompletion20261011 ratio
      (holdingGlobalSkorokhodSampleCompletion20261011 acceleration placement sample) =
    holdingGlobalSkorokhodSampleCompletion20261011 (acceleration*(ratio:ℝ)) placement sample := by
  apply congrArg SkorokhodGlobalPathCompletion20261011.mk
  funext time
  change placement (holdingTimePath sample.1 sample.2 (acceleration*((ratio*time:ℝ≥0):ℝ))) =
    placement (holdingTimePath sample.1 sample.2 ((acceleration*(ratio:ℝ))*(time:ℝ)))
  rw [NNReal.coe_mul, mul_assoc]

theorem timeScale_discrete_sample_identity_completion20261011
    (ratio : ℝ≥0) (acceleration : ℝ) (placement : Vertex → Space) (trajectory : ℕ → Vertex) :
    skorokhodGlobalTimeScaleCompletion20261011 ratio
      (discreteGlobalSkorokhodSampleCompletion20261011 acceleration placement trajectory) =
    discreteGlobalSkorokhodSampleCompletion20261011 (acceleration*(ratio:ℝ)) placement trajectory := by
  apply congrArg SkorokhodGlobalPathCompletion20261011.mk
  funext time
  change placement (trajectory ⌊acceleration*((ratio*time:ℝ≥0):ℝ)⌋₊) =
    placement (trajectory ⌊(acceleration*(ratio:ℝ))*(time:ℝ)⌋₊)
  rw [NNReal.coe_mul, mul_assoc]

theorem timeScale_holding_sample_aemeasurable_completion20261011
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (ratio : ℝ≥0) (ratioPositive : 0 < ratio)
    (acceleration : ℝ) (accelerationPositive : 0 < acceleration) (placement : Vertex → Space) :
    AEMeasurable (fun sample => skorokhodGlobalTimeScaleCompletion20261011 ratio
      (holdingGlobalSkorokhodSampleCompletion20261011 acceleration placement sample)) law := by
  simpa only [timeScale_holding_sample_identity_completion20261011] using
    holdingGlobalSkorokhodSample_aemeasurable_completion20261011 law regular (acceleration*(ratio:ℝ))
      (mul_pos accelerationPositive (NNReal.coe_pos.mpr ratioPositive)) placement

theorem timeScale_discrete_sample_measurable_completion20261011
    (ratio : ℝ≥0) (acceleration : ℝ) (accelerationNonnegative : 0 ≤ acceleration) (placement : Vertex → Space) :
    Measurable (fun trajectory => skorokhodGlobalTimeScaleCompletion20261011 ratio
      (discreteGlobalSkorokhodSampleCompletion20261011 acceleration placement trajectory)) := by
  simpa only [timeScale_discrete_sample_identity_completion20261011] using
    discreteGlobalSkorokhodSample_measurable_completion20261011 (acceleration*(ratio:ℝ))
      (mul_nonneg accelerationNonnegative ratio.property) placement

end
end IGSIII34.Diffusion

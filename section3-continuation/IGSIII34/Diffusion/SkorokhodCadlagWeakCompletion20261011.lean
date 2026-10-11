import IGSIII34.Diffusion.SkorokhodCadlagSampleCompletion20261011
import IGSIII34.Diffusion.ProbabilitySubtypeWeakCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def holdingCadlagProbabilityCompletion20261011
    {Vertex : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space) :=
  law.map (holdingCadlagSample_aemeasurable_completion20261011 (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement)

theorem holdingCadlagProbability_val_completion20261011
    {Vertex : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (holdingCadlagProbabilityCompletion20261011 law regular scale scalePositive placement).map measurable_subtype_coe.aemeasurable =
      law.map (holdingGlobalSkorokhodSample_aemeasurable_completion20261011 (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement) := by
  apply Subtype.ext
  exact holdingCadlagSample_map_val_completion20261011 (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement

def continuousCadlagProbabilityCompletion20261011 {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space) :=
  law.map (continuousCadlagSample_measurable_completion20261011 sample continuous evaluations).aemeasurable

theorem continuousCadlagProbability_val_completion20261011 {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    (continuousCadlagProbabilityCompletion20261011 law sample continuous evaluations).map measurable_subtype_coe.aemeasurable =
      law.map (continuousGlobalFamily_measurable_completion20261011 sample continuous evaluations).aemeasurable := by
  apply Subtype.ext
  change ((law : Measure Outcome).map (continuousCadlagSampleCompletion20261011 sample continuous)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe (continuousCadlagSample_measurable_completion20261011 sample continuous evaluations)]
  rfl

/-- Actual holding-time path convergence on the ambient time-change
carrier is also weak convergence on genuine cadlag paths. The sole repair
is on the original clock-null event; the pushed original path law is
preserved exactly. -/
theorem holdingCadlagProbability_weak_of_global_weak_completion20261011
    {Vertices : ℕ → Type*} [∀ index, MeasurableSpace (Vertices index)]
    [∀ index, Fintype (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    (laws : ∀ index, ProbabilityMeasure ((ℕ → Vertices index) × (ℕ → ℝ)))
    (regular : ∀ index, ∀ᵐ sample ∂(laws index : Measure ((ℕ → Vertices index) × (ℕ → ℝ))), (∀ jump, 0 < sample.2 jump) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scales : ℕ → ℝ) (scalesPositive : ∀ index, 0 < scales index)
    (placements : ∀ index, Vertices index → Space)
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (weak : Tendsto (fun index => (laws index).map
      (holdingGlobalSkorokhodSample_aemeasurable_completion20261011 (laws index : Measure ((ℕ → Vertices index) × (ℕ → ℝ)))
        (regular index) (scales index) (scalesPositive index) (placements index))) atTop
      (𝓝 (law.map (continuousGlobalFamily_measurable_completion20261011 sample continuous evaluations).aemeasurable))) :
    Tendsto (fun index => holdingCadlagProbabilityCompletion20261011 (laws index) (regular index)
      (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (continuousCadlagProbabilityCompletion20261011 law sample continuous evaluations)) := by
  apply probability_subtype_weak_of_val_weak_completion20261011
    (fun path : SkorokhodGlobalPathCompletion20261011 Space => SkorokhodCadlagCompletion20261011 path)
  simpa only [holdingCadlagProbability_val_completion20261011, continuousCadlagProbability_val_completion20261011] using weak

end
end IGSIII34.Diffusion


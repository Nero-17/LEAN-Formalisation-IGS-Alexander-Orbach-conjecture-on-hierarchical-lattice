import IGSIII34.Diffusion.SkorokhodCadlagSampleCompletion
import IGSIII34.Diffusion.ProbabilitySubtypeWeakCompletion

set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def holdingCadlagProbabilityCompletion
    {Vertex : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion Space) :=
  law.map (holdingCadlagSample_aemeasurable_completion (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement)

theorem holdingCadlagProbability_val_completion
    {Vertex : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (holdingCadlagProbabilityCompletion law regular scale scalePositive placement).map measurable_subtype_coe.aemeasurable =
      law.map (holdingGlobalSkorokhodSample_aemeasurable_completion (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement) := by
  apply Subtype.ext
  exact holdingCadlagSample_map_val_completion (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))) regular scale scalePositive placement

def continuousCadlagProbabilityCompletion {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion Space) :=
  law.map (continuousCadlagSample_measurable_completion sample continuous evaluations).aemeasurable

theorem continuousCadlagProbability_val_completion {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    (continuousCadlagProbabilityCompletion law sample continuous evaluations).map measurable_subtype_coe.aemeasurable =
      law.map (continuousGlobalFamily_measurable_completion sample continuous evaluations).aemeasurable := by
  apply Subtype.ext
  change ((law : Measure Outcome).map (continuousCadlagSampleCompletion sample continuous)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe (continuousCadlagSample_measurable_completion sample continuous evaluations)]
  rfl

/-- Actual holding-time path convergence on the ambient time-change
carrier is also weak convergence on genuine cadlag paths. The sole repair
is on the original clock-null event; the pushed original path law is
preserved exactly. -/
theorem holdingCadlagProbability_weak_of_global_weak_completion
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
      (holdingGlobalSkorokhodSample_aemeasurable_completion (laws index : Measure ((ℕ → Vertices index) × (ℕ → ℝ)))
        (regular index) (scales index) (scalesPositive index) (placements index))) atTop
      (𝓝 (law.map (continuousGlobalFamily_measurable_completion sample continuous evaluations).aemeasurable))) :
    Tendsto (fun index => holdingCadlagProbabilityCompletion (laws index) (regular index)
      (scales index) (scalesPositive index) (placements index)) atTop
      (𝓝 (continuousCadlagProbabilityCompletion law sample continuous evaluations)) := by
  apply probability_subtype_weak_of_val_weak_completion
    (fun path : SkorokhodGlobalPathCompletion Space => SkorokhodCadlagCompletion path)
  simpa only [holdingCadlagProbability_val_completion, continuousCadlagProbability_val_completion] using weak

end
end IGSIII34.Diffusion


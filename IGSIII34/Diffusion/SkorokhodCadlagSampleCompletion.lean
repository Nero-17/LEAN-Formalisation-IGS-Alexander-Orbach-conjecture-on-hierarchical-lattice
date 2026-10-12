import IGSIII34.Diffusion.ActualHoldingSkorokhodMeasurabilityCompletion
import IGSIII34.Diffusion.SkorokhodGlobalContinuousSampleCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Space Vertex : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]

/-- The genuine right-continuous, left-limit path carrier, with the
subspace topology of integer-horizon time-change J1. -/
abbrev SkorokhodCadlagPathCompletion (Space : Type*) [MetricSpace Space] [CompactSpace Space] :=
  {path : SkorokhodGlobalPathCompletion Space // SkorokhodCadlagCompletion path}

def holdingCadlagSampleCompletion (scale : ℝ) (scalePositive : 0 < scale)
    (placement : Vertex → Space) (sample : (ℕ → Vertex) × (ℕ → ℝ)) :
    SkorokhodCadlagPathCompletion Space := by
  classical
  exact if regular : (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop then
    ⟨holdingGlobalSkorokhodSampleCompletion scale placement sample,
      holdingTimePath_cadlag_completion placement sample.1 sample.2 regular.1 regular.2 scale scalePositive⟩
  else
    ⟨⟨fun _ => placement (sample.1 0)⟩,
      continuous_path_cadlag_completion _ continuous_const⟩

theorem holdingCadlagSample_val_ae_completion
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (fun sample => (holdingCadlagSampleCompletion scale scalePositive placement sample).val) =ᵐ[law]
      holdingGlobalSkorokhodSampleCompletion scale placement := by
  filter_upwards [regular] with sample clock
  simp only [holdingCadlagSampleCompletion, dif_pos clock]

theorem holdingCadlagSample_aemeasurable_completion
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    AEMeasurable (holdingCadlagSampleCompletion scale scalePositive placement) law := by
  have underlying := (holdingGlobalSkorokhodSample_aemeasurable_completion law regular scale scalePositive placement).congr
    (holdingCadlagSample_val_ae_completion law regular scale scalePositive placement).symm
  exact underlying.subtype_mk

theorem holdingCadlagSample_map_val_completion
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (law.map (holdingCadlagSampleCompletion scale scalePositive placement)).map Subtype.val =
      law.map (holdingGlobalSkorokhodSampleCompletion scale placement) := by
  rw [AEMeasurable.map_map_of_aemeasurable measurable_subtype_coe.aemeasurable
    (holdingCadlagSample_aemeasurable_completion law regular scale scalePositive placement)]
  exact Measure.map_congr (holdingCadlagSample_val_ae_completion law regular scale scalePositive placement)

def discreteCadlagSampleCompletion (scale : ℝ) (scalePositive : 0 < scale)
    (placement : Vertex → Space) (trajectory : ℕ → Vertex) :
    SkorokhodCadlagPathCompletion Space :=
  ⟨discreteGlobalSkorokhodSampleCompletion scale placement trajectory,
    fixedClockPath_cadlag_completion placement trajectory scale scalePositive⟩

theorem discreteCadlagSample_measurable_completion
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    Measurable (discreteCadlagSampleCompletion scale scalePositive placement) :=
  (discreteGlobalSkorokhodSample_measurable_completion scale scalePositive.le placement).subtype_mk

def continuousCadlagSampleCompletion {Outcome : Type*}
    (sample : Outcome → ℝ≥0 → Space) (continuous : ∀ outcome, Continuous (sample outcome))
    (outcome : Outcome) : SkorokhodCadlagPathCompletion Space :=
  ⟨⟨sample outcome⟩, continuous_path_cadlag_completion _ (continuous outcome)⟩

theorem continuousCadlagSample_measurable_completion {Outcome : Type*} [MeasurableSpace Outcome]
    (sample : Outcome → ℝ≥0 → Space) (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    Measurable (continuousCadlagSampleCompletion sample continuous) :=
  (continuousGlobalFamily_measurable_completion sample continuous evaluations).subtype_mk

end
end IGSIII34.Diffusion

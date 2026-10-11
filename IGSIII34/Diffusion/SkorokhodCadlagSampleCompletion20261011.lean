import IGSIII34.Diffusion.ActualHoldingSkorokhodMeasurabilityCompletion20261011
import IGSIII34.Diffusion.SkorokhodGlobalContinuousSampleCompletion20261011

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
abbrev SkorokhodCadlagPathCompletion20261011 (Space : Type*) [MetricSpace Space] [CompactSpace Space] :=
  {path : SkorokhodGlobalPathCompletion20261011 Space // SkorokhodCadlagCompletion20261011 path}

def holdingCadlagSampleCompletion20261011 (scale : ℝ) (scalePositive : 0 < scale)
    (placement : Vertex → Space) (sample : (ℕ → Vertex) × (ℕ → ℝ)) :
    SkorokhodCadlagPathCompletion20261011 Space := by
  classical
  exact if regular : (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop then
    ⟨holdingGlobalSkorokhodSampleCompletion20261011 scale placement sample,
      holdingTimePath_cadlag_completion20261011 placement sample.1 sample.2 regular.1 regular.2 scale scalePositive⟩
  else
    ⟨⟨fun _ => placement (sample.1 0)⟩,
      continuous_path_cadlag_completion20261011 _ continuous_const⟩

theorem holdingCadlagSample_val_ae_completion20261011
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (fun sample => (holdingCadlagSampleCompletion20261011 scale scalePositive placement sample).val) =ᵐ[law]
      holdingGlobalSkorokhodSampleCompletion20261011 scale placement := by
  filter_upwards [regular] with sample clock
  simp only [holdingCadlagSampleCompletion20261011, dif_pos clock]

theorem holdingCadlagSample_aemeasurable_completion20261011
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    AEMeasurable (holdingCadlagSampleCompletion20261011 scale scalePositive placement) law := by
  have underlying := (holdingGlobalSkorokhodSample_aemeasurable_completion20261011 law regular scale scalePositive placement).congr
    (holdingCadlagSample_val_ae_completion20261011 law regular scale scalePositive placement).symm
  exact underlying.subtype_mk

theorem holdingCadlagSample_map_val_completion20261011
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    (law.map (holdingCadlagSampleCompletion20261011 scale scalePositive placement)).map Subtype.val =
      law.map (holdingGlobalSkorokhodSampleCompletion20261011 scale placement) := by
  rw [AEMeasurable.map_map_of_aemeasurable measurable_subtype_coe.aemeasurable
    (holdingCadlagSample_aemeasurable_completion20261011 law regular scale scalePositive placement)]
  exact Measure.map_congr (holdingCadlagSample_val_ae_completion20261011 law regular scale scalePositive placement)

def discreteCadlagSampleCompletion20261011 (scale : ℝ) (scalePositive : 0 < scale)
    (placement : Vertex → Space) (trajectory : ℕ → Vertex) :
    SkorokhodCadlagPathCompletion20261011 Space :=
  ⟨discreteGlobalSkorokhodSampleCompletion20261011 scale placement trajectory,
    fixedClockPath_cadlag_completion20261011 placement trajectory scale scalePositive⟩

theorem discreteCadlagSample_measurable_completion20261011
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    Measurable (discreteCadlagSampleCompletion20261011 scale scalePositive placement) :=
  (discreteGlobalSkorokhodSample_measurable_completion20261011 scale scalePositive.le placement).subtype_mk

def continuousCadlagSampleCompletion20261011 {Outcome : Type*}
    (sample : Outcome → ℝ≥0 → Space) (continuous : ∀ outcome, Continuous (sample outcome))
    (outcome : Outcome) : SkorokhodCadlagPathCompletion20261011 Space :=
  ⟨⟨sample outcome⟩, continuous_path_cadlag_completion20261011 _ (continuous outcome)⟩

theorem continuousCadlagSample_measurable_completion20261011 {Outcome : Type*} [MeasurableSpace Outcome]
    (sample : Outcome → ℝ≥0 → Space) (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    Measurable (continuousCadlagSampleCompletion20261011 sample continuous) :=
  (continuousGlobalFamily_measurable_completion20261011 sample continuous evaluations).subtype_mk

end
end IGSIII34.Diffusion

import IGSIII34.Diffusion.SkorokhodGlobalJumpMeasurabilityCompletion20261011
import IGSIII34.Diffusion.HoldingFiniteJumpRepresentationCompletion20261011
import IGSIII34.Diffusion.ContinuousWalkConstruction
import IGSIII34.Diffusion.ActualCadlagPathsCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Space Vertex Edge : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]

def holdingGlobalSkorokhodSampleCompletion20261011 (scale : ℝ) (placement : Vertex → Space)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) : SkorokhodGlobalPathCompletion20261011 Space :=
  ⟨fun time => placement (holdingTimePath sample.1 sample.2 (scale * (time : ℝ)))⟩

theorem holdingGlobalSkorokhodSample_aemeasurable_completion20261011
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂law, (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    AEMeasurable (holdingGlobalSkorokhodSampleCompletion20261011 scale placement) law := by
  apply skorokhodGlobal_jump_sample_aemeasurable_completion20261011 law
    (fun sample time => placement (holdingTimePath sample.1 sample.2 (scale * (time : ℝ))))
    (fun time => (measurable_of_finite placement).comp (holdingTimePath_measurable (scale * (time : ℝ))))
  filter_upwards [regular] with sample clock
  intro horizon
  have physicalPositive : 0 < scale * (horizon+1 : ℝ) := mul_pos scalePositive (by positivity)
  obtain ⟨count, knots, increasing, interior, representation⟩ :=
    holdingTimePath_finite_interior_jump_representation_completion20261011
      (fun index => placement (sample.1 index)) sample.2 clock.1 clock.2
      (scale * (horizon+1 : ℝ)) physicalPositive
  refine ⟨count, knots, increasing, interior, (fun index : Fin (count+1) => placement (sample.1 index.val)),
    placement (holdingTimePath sample.1 sample.2 (scale * (horizon+1 : ℝ))), ?_⟩
  apply congrArg SkorokhodIntervalPathCompletion20261011.mk
  funext time
  by_cases terminal : time.val = 1
  · simp only [skorokhodIntegerProfileCompletion20261011,
      finiteEndpointJumpIntervalPathCompletion20261011, terminal, if_true,
      NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    change placement (holdingTimePath sample.1 sample.2 (scale * ((horizon+1 : ℝ) * 1))) = _
    rw [mul_one]
  · have before : time.val < 1 := lt_of_le_of_ne time.property.2 terminal
    simp only [skorokhodIntegerProfileCompletion20261011,
      finiteEndpointJumpIntervalPathCompletion20261011, terminal, if_false,
      NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    change holdingTimePath (fun index => placement (sample.1 index)) sample.2
      (scale * ((horizon+1 : ℝ) * time.val)) = _
    rw [← mul_assoc]
    exact representation time before

def finiteContinuousGlobalSkorokhodProbabilityCompletion20261011 [DecidableEq Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodGlobalPathCompletion20261011 Space) :=
  ProbabilityMeasure.map
    (⟨finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex), inferInstance⟩ :
      ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (holdingGlobalSkorokhodSample_aemeasurable_completion20261011 _
      ((finiteContinuousWalkSampleLaw_regular endpoint positiveDegree (initial : Measure Vertex)).mono
        (fun sample clock => ⟨clock.1, clock.2.1⟩)) scale scalePositive placement)

end
end IGSIII34.Diffusion

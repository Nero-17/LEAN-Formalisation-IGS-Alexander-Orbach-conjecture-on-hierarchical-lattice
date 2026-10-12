import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology

/-- The continuous mapping theorem requires continuity only almost
everywhere for the limiting probability. The proof uses the closure of a
closed-set preimage and the genuine portmanteau inequality, without a
separability or tightness assumption on the ambient path carrier. -/
theorem probability_weak_map_of_ae_continuous_completion
    {First Second : Type*} [PseudoMetricSpace First] [MeasurableSpace First] [BorelSpace First]
    [TopologicalSpace Second] [MeasurableSpace Second] [OpensMeasurableSpace Second]
    (laws : ℕ → ProbabilityMeasure First) (law : ProbabilityMeasure First)
    (weak : Tendsto laws atTop (𝓝 law)) (map : First → Second)
    (measurable : ∀ index, AEMeasurable map (laws index : Measure First))
    (limitMeasurable : AEMeasurable map (law : Measure First))
    (continuous : ∀ᵐ point ∂(law : Measure First), ContinuousAt map point) :
    Tendsto (fun index => (laws index).map (measurable index)) atTop (𝓝 (law.map limitMeasurable)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro closed closedSet
  have closureBound : (law : Measure First) (closure (map ⁻¹' closed)) ≤ (law : Measure First) (map ⁻¹' closed) := by
    apply measure_mono_ae
    filter_upwards [continuous] with point continuity
    intro member
    have imageMember := mem_closure_image continuity member
    exact closedSet.closure_eq ▸ (closure_mono (image_preimage_subset map closed)) imageMember
  have weakClosed := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto weak
    (isClosed_closure : IsClosed (closure (map ⁻¹' closed)))
  calc
    limsup (fun index => ((laws index).map (measurable index) : Measure Second) closed) atTop ≤
        limsup (fun index => (laws index : Measure First) (closure (map ⁻¹' closed))) atTop := by
      apply limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
      apply Eventually.of_forall
      intro index
      dsimp only
      rw [ProbabilityMeasure.map_apply' _ _ closedSet.measurableSet]
      exact measure_mono subset_closure
    _ ≤ (law : Measure First) (closure (map ⁻¹' closed)) := weakClosed
    _ ≤ (law : Measure First) (map ⁻¹' closed) := closureBound
    _ = (law.map limitMeasurable : Measure Second) closed :=
      (ProbabilityMeasure.map_apply' _ _ closedSet.measurableSet).symm

end
end IGSIII34.Diffusion

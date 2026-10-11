import IGSIII34.Diffusion.PathWeakAEReconstructionCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

/-- A genuine coupling that is close in probability transfers full weak
path convergence. No convergence of only cylinder observations is used. -/
theorem probability_ae_sample_weak_transfer_completion20261011
    {Path Outcome : Type*} [PseudoMetricSpace Path]
    [MeasurableSpace Path] [OpensMeasurableSpace Path] [MeasurableSpace Outcome]
    {Samples : ℕ → Type*} [∀ index, MeasurableSpace (Samples index)]
    (laws : ∀ index, Measure (Samples index)) [∀ index, IsProbabilityMeasure (laws index)]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (samples approximations : ∀ index, Samples index → Path) (sample : Outcome → Path)
    (samplesMeasurable : ∀ index, AEMeasurable (samples index) (laws index))
    (approximationsMeasurable : ∀ index, AEMeasurable (approximations index) (laws index))
    (sampleMeasurable : AEMeasurable sample law)
    (weakApproximations : Tendsto (fun index => ProbabilityMeasure.map
      (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index)) (approximationsMeasurable index)) atTop
        (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome) sampleMeasurable)))
    (closeness : ∀ duration error : ℝ, 0 < duration → 0 < error →
      ∀ᶠ index in atTop, ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
        ∀ outcome, outcome ∉ bad → dist (samples index outcome) (approximations index outcome) ≤ duration) :
    Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
      (samplesMeasurable index)) atTop
      (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome) sampleMeasurable)) := by
  apply probability_ae_sample_weak_of_reconstructions_completion20261011 laws law samples sample
    samplesMeasurable sampleMeasurable (fun _ => approximations) (fun _ => sample)
    (fun _ => approximationsMeasurable) (fun _ => sampleMeasurable) (fun _ => weakApproximations)
  intro duration error durationPositive errorPositive
  refine ⟨0, closeness duration error durationPositive errorPositive, ∅, MeasurableSet.empty, ?_, ?_⟩
  · simpa only [Measure.real, measure_empty, ENNReal.toReal_zero] using errorPositive.le
  · intro outcome _
    simpa only [dist_self] using durationPositive.le

end
end IGSIII34.Diffusion


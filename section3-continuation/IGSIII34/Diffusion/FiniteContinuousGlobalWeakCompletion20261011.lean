import IGSIII34.Diffusion.CTGlobalCouplingProbabilityCompletion20261011
import IGSIII34.Diffusion.ActualHoldingSkorokhodMeasurabilityCompletion20261011
import IGSIII34.Diffusion.PathWeakAECouplingTransferCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

/-- Genuine full-path weak convergence for the continuous-time original
finite graph walks follows by their actual independent exponential-clock
coupling to the fixed-clock walks. -/
theorem finiteContinuous_global_weak_of_discrete_completion20261011
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth))
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop)
    (placement : ∀ depth, Vertices depth → Space)
    (target : ProbabilityMeasure (SkorokhodGlobalPathCompletion20261011 Space))
    (discreteWeak : Tendsto (fun depth => discreteGlobalSkorokhodProbabilityCompletion20261011
      (endpoint depth) (positiveDegree depth) (initial depth) (acceleration depth) (accelerationPositive depth).le (placement depth))
      atTop (𝓝 target))
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion20261011 (placement depth) (acceleration depth) horizon duration tolerance) ≤ error) :
    Tendsto (fun depth => finiteContinuousGlobalSkorokhodProbabilityCompletion20261011
      (endpoint depth) (positiveDegree depth) (initial depth) (acceleration depth) (accelerationPositive depth) (placement depth))
      atTop (𝓝 target) := by
  let laws := fun depth => finiteContinuousWalkSampleLaw (endpoint depth) (positiveDegree depth) (initial depth : Measure (Vertices depth))
  let samples := fun depth => holdingGlobalSkorokhodSampleCompletion20261011 (acceleration depth) (placement depth)
  let approximations := fun depth (outcome : (ℕ → Vertices depth) × (ℕ → ℝ)) =>
    discreteGlobalSkorokhodSampleCompletion20261011 (acceleration depth) (placement depth) outcome.1
  have sampleMeasurable (depth : ℕ) : AEMeasurable (samples depth) (laws depth) :=
    holdingGlobalSkorokhodSample_aemeasurable_completion20261011 _
      ((finiteContinuousWalkSampleLaw_regular (endpoint depth) (positiveDegree depth) (initial depth : Measure (Vertices depth))).mono
        (fun outcome regular => ⟨regular.1, regular.2.1⟩)) _ (accelerationPositive depth) _
  have approximationMeasurable (depth : ℕ) : Measurable (approximations depth) :=
    (discreteGlobalSkorokhodSample_measurable_completion20261011 _ (accelerationPositive depth).le _).comp measurable_fst
  have approximationLaw (depth : ℕ) : ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure ((ℕ → Vertices depth) × (ℕ → ℝ)))
      (approximationMeasurable depth).aemeasurable = discreteGlobalSkorokhodProbabilityCompletion20261011
        (endpoint depth) (positiveDegree depth) (initial depth) (acceleration depth) (accelerationPositive depth).le (placement depth) := by
    apply Subtype.ext
    change ((finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).prod exponentialHoldingTimeLaw).map
      (discreteGlobalSkorokhodSampleCompletion20261011 (acceleration depth) (placement depth) ∘ Prod.fst) =
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).map
          (discreteGlobalSkorokhodSampleCompletion20261011 (acceleration depth) (placement depth))
    rw [← Measure.map_map (discreteGlobalSkorokhodSample_measurable_completion20261011 _ (accelerationPositive depth).le _) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
  have targetLaw : ProbabilityMeasure.map (⟨(target : Measure (SkorokhodGlobalPathCompletion20261011 Space)), inferInstance⟩ : ProbabilityMeasure _)
      (measurable_id.aemeasurable : AEMeasurable (id : SkorokhodGlobalPathCompletion20261011 Space → _) (target : Measure _)) = target := by
    apply Subtype.ext
    change (target : Measure (SkorokhodGlobalPathCompletion20261011 Space)).map id =
      (target : Measure (SkorokhodGlobalPathCompletion20261011 Space))
    rw [Measure.map_id]
  have approximationWeak : Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure ((ℕ → Vertices depth) × (ℕ → ℝ))) (approximationMeasurable depth).aemeasurable)
      atTop (𝓝 (ProbabilityMeasure.map (⟨(target : Measure (SkorokhodGlobalPathCompletion20261011 Space)), inferInstance⟩ : ProbabilityMeasure _)
        (measurable_id.aemeasurable : AEMeasurable (id : SkorokhodGlobalPathCompletion20261011 Space → _) (target : Measure _)))) := by
    simpa only [approximationLaw, targetLaw] using discreteWeak
  have transferred := probability_ae_sample_weak_transfer_completion20261011 laws
    (target : Measure (SkorokhodGlobalPathCompletion20261011 Space)) samples approximations id
    sampleMeasurable (fun depth => (approximationMeasurable depth).aemeasurable) measurable_id.aemeasurable approximationWeak
    (continuousClock_global_coupling_probability_completion20261011 Vertices
      (fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth))
      placement acceleration accelerationPositive diverge chainModulus samples
      (fun depth => Eventually.of_forall (fun outcome time => rfl)))
  rw [targetLaw] at transferred
  convert transferred using 1
  funext depth
  apply Subtype.ext
  rfl

end
end IGSIII34.Diffusion

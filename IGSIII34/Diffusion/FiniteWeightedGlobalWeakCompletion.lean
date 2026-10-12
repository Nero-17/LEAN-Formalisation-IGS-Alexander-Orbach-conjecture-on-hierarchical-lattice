import IGSIII34.Diffusion.WeightedClockCouplingProbabilityCompletion
import IGSIII34.Diffusion.CompactUniformGlobalCouplingCompletion
import IGSIII34.Diffusion.FiniteContinuousGlobalWeakCompletion

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def finiteWeightedGlobalSkorokhodProbabilityCompletion
    {Vertex Edge : Type*} [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (scale : ℝ) (scalePositive : 0 < scale) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodGlobalPathCompletion Space) :=
  ProbabilityMeasure.map
    (⟨finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex), inferInstance⟩ :
      ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (weightedHoldingGlobalSample_aemeasurable_completion _ weight weightPositive
      ((finiteContinuousWalkSampleLaw_regular endpoint positiveDegree (initial : Measure Vertex)).mono
        (fun _ regular => ⟨regular.1, regular.2.1⟩)) scale scalePositive placement)

/-- The actual weighted exponential finite walk laws converge on the entire
time-change path space. The clock corrector premise is an additive finite
chain estimate, not a desired path-convergence or process-existence hypothesis. -/
theorem finiteWeighted_global_weak_of_discrete_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, Nonempty (Vertices depth)]
    [∀ depth, DecidableEq (Vertices depth)] [∀ depth, MeasurableSpace (Vertices depth)]
    [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth))
    (weights : ∀ depth, Vertices depth → ℝ) (weightsPositive : ∀ depth vertex, 0 < weights depth vertex)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (weightsBounded : ∀ depth vertex, weights depth vertex ≤ bound)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop) (placement : ∀ depth, Vertices depth → Space)
    (centeredClock : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth))
        {trajectory | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧ acceleration depth * tolerance <
          |centeredWeightClockCompletion (fun index => weights depth (trajectory index)) count|}) atTop (𝓝 0))
    (target : ProbabilityMeasure (SkorokhodGlobalPathCompletion Space))
    (discreteWeak : Tendsto (fun depth => discreteGlobalSkorokhodProbabilityCompletion
      (endpoint depth) (positiveDegree depth) (initial depth) (acceleration depth) (accelerationPositive depth).le (placement depth))
      atTop (𝓝 target))
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion (placement depth) (acceleration depth) horizon duration tolerance) ≤ error) :
    Tendsto (fun depth => finiteWeightedGlobalSkorokhodProbabilityCompletion
      (endpoint depth) (positiveDegree depth) (initial depth) (weights depth) (weightsPositive depth)
      (acceleration depth) (accelerationPositive depth) (placement depth)) atTop (𝓝 target) := by
  let laws := fun depth => finiteContinuousWalkSampleLaw (endpoint depth) (positiveDegree depth) (initial depth : Measure (Vertices depth))
  let samples := fun depth => weightedHoldingGlobalSampleCompletion (weights depth) (acceleration depth) (placement depth)
  let approximations := fun depth (outcome : (ℕ → Vertices depth) × (ℕ → ℝ)) =>
    discreteGlobalSkorokhodSampleCompletion (acceleration depth) (placement depth) outcome.1
  have sampleMeasurable (depth : ℕ) : AEMeasurable (samples depth) (laws depth) :=
    weightedHoldingGlobalSample_aemeasurable_completion ⟨laws depth, inferInstance⟩ (weights depth) (weightsPositive depth)
      ((finiteContinuousWalkSampleLaw_regular (endpoint depth) (positiveDegree depth) (initial depth : Measure (Vertices depth))).mono
        (fun _ regular => ⟨regular.1, regular.2.1⟩)) _ (accelerationPositive depth) _
  have approximationMeasurable (depth : ℕ) : Measurable (approximations depth) :=
    (discreteGlobalSkorokhodSample_measurable_completion _ (accelerationPositive depth).le _).comp measurable_fst
  have approximationLaw (depth : ℕ) : ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure ((ℕ → Vertices depth) × (ℕ → ℝ)))
      (approximationMeasurable depth).aemeasurable = discreteGlobalSkorokhodProbabilityCompletion
        (endpoint depth) (positiveDegree depth) (initial depth) (acceleration depth) (accelerationPositive depth).le (placement depth) := by
    apply Subtype.ext
    change ((finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).prod exponentialHoldingTimeLaw).map
      (discreteGlobalSkorokhodSampleCompletion (acceleration depth) (placement depth) ∘ Prod.fst) =
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).map
          (discreteGlobalSkorokhodSampleCompletion (acceleration depth) (placement depth))
    rw [← Measure.map_map (discreteGlobalSkorokhodSample_measurable_completion _ (accelerationPositive depth).le _) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
  have targetLaw : ProbabilityMeasure.map (⟨(target : Measure (SkorokhodGlobalPathCompletion Space)), inferInstance⟩ : ProbabilityMeasure _) (measurable_id.aemeasurable : AEMeasurable
      (id : SkorokhodGlobalPathCompletion Space → _) (target : Measure _)) = target := by
    apply Subtype.ext
    change (target : Measure (SkorokhodGlobalPathCompletion Space)).map id = (target : Measure (SkorokhodGlobalPathCompletion Space))
    rw [Measure.map_id]
  have approximationWeak : Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure ((ℕ → Vertices depth) × (ℕ → ℝ))) (approximationMeasurable depth).aemeasurable)
      atTop (𝓝 (ProbabilityMeasure.map (⟨(target : Measure (SkorokhodGlobalPathCompletion Space)), inferInstance⟩ : ProbabilityMeasure _) (measurable_id.aemeasurable : AEMeasurable
        (id : SkorokhodGlobalPathCompletion Space → _) (target : Measure _)))) := by
    simpa only [approximationLaw, targetLaw] using discreteWeak
  have compactCoupling : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∀ᶠ depth in atTop, ∃ bad : Set ((ℕ → Vertices depth) × (ℕ → ℝ)), MeasurableSet bad ∧
        (laws depth).real bad ≤ error ∧ ∀ outcome ∉ bad, ∀ time : ℝ≥0, (time : ℝ) ≤ horizon →
          dist (samples depth outcome time) (approximations depth outcome time) ≤ tolerance := by
    intro horizon tolerance error tolerancePositive errorPositive
    have coupling := weightedClock_uniform_coupling_probability_completion Vertices
      (fun depth => (⟨finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth), inferInstance⟩ :
        ProbabilityMeasure (ℕ → Vertices depth))) placement weights weightsPositive bound boundNonnegative weightsBounded
      acceleration accelerationPositive diverge centeredClock chainModulus horizon tolerance error tolerancePositive errorPositive
    filter_upwards [coupling] with depth coupled
    obtain ⟨bad, measurable, probability, uniform⟩ := coupled
    exact ⟨bad, measurable, probability, fun outcome outside time before => uniform outcome outside time time.property before⟩
  have wholeCoupling := compact_uniform_global_coupling_probability_completion
    (fun depth => (ℕ → Vertices depth) × (ℕ → ℝ)) laws samples approximations compactCoupling
  have transferred := probability_ae_sample_weak_transfer_completion laws
    (target : Measure (SkorokhodGlobalPathCompletion Space)) samples approximations id
    sampleMeasurable (fun depth => (approximationMeasurable depth).aemeasurable) measurable_id.aemeasurable approximationWeak wholeCoupling
  rw [targetLaw] at transferred
  convert transferred using 1
  funext depth
  apply Subtype.ext
  rfl

end
end IGSIII34.Diffusion

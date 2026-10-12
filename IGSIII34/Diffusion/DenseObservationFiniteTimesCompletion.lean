import IGSIII34.Diffusion.PathWeakReconstructionCompletion
import IGSIII34.Diffusion.FlooredRealTimeModulusCompletion
import IGSIII34.Diffusion.CountablePathMeasurableExtensionCompletion
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def finiteFlooredTimeSampleCompletion {Vertex : Type*} {count : ℕ}
    (scale : ℝ) (times : Fin count → ℝ≥0) (placement : Vertex → Space) (path : ℕ → Vertex) : Fin count → Space :=
  fun index => placement (path ⌊scale * (times index : ℝ)⌋₊)

theorem finiteFlooredTimeSample_measurable_completion
    {Vertex : Type*} [Fintype Vertex] [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] {count : ℕ}
    (scale : ℝ) (times : Fin count → ℝ≥0) (placement : Vertex → Space) :
    Measurable (finiteFlooredTimeSampleCompletion scale times placement) :=
  measurable_pi_lambda _ fun index => (measurable_of_finite placement).comp (measurable_pi_apply ⌊scale * (times index : ℝ)⌋₊)

/-- A dense countable observation limit and the proved original-chain
modulus bounds already imply the true finite-dimensional weak limit at
arbitrary real times. No Markov or finite-dimensional convergence premise
is inserted. -/
theorem finiteFlooredTimeLaw_weak_of_dense_observations_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth)) (scales : ℕ → ℝ) (scaleNonnegative : ∀ depth, 0 ≤ scales depth)
    (placement : ∀ depth, Vertices depth → Space)
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (limitLaw : ProbabilityMeasure (ℕ → Space))
    (weak : Tendsto (fun depth => discreteRescaledObservationLawCompletion (endpoint depth) (positiveDegree depth)
      (initial depth) (scales depth) times (placement depth)) atTop (𝓝 limitLaw))
    (regular : ∀ᵐ path ∂(limitLaw : Measure (ℕ → Space)), countableTimeLocalUniformContinuityCompletion times path)
    {count : ℕ} (futureTimes : Fin count → ℝ≥0) (horizon : ℕ)
    (within : ∀ index, (futureTimes index : ℝ) + 1 ≤ horizon)
    (chainModulus : ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion (placement depth) (scales depth) horizon duration tolerance) ≤ error) :
    Tendsto (fun depth => (discreteWalkProbabilityCompletion (endpoint depth) (positiveDegree depth) (initial depth)).map
      (finiteFlooredTimeSample_measurable_completion (scales depth) futureTimes (placement depth)).aemeasurable) atTop
      (𝓝 (limitLaw.map (show AEMeasurable (fun path : ℕ → Space => fun index : Fin count =>
        countableTimeContinuousSampleCompletion times dense path (futureTimes index)) (limitLaw : Measure (ℕ → Space)) from
        (measurable_pi_lambda _ fun index => countableTimeContinuousSample_evaluation_measurable_completion times dense (futureTimes index)).aemeasurable))) := by
  classical
  have radiusPositive (grid : ℕ) : 0 < 1 / (grid + 1 : ℝ) := by positivity
  choose coordinates close using fun (grid : ℕ) (index : Fin count) => dense.exists_dist_lt (futureTimes index) (radiusPositive grid)
  have meshConvergence : Tendsto (fun grid : ℕ => 1 / (grid + 1 : ℝ)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have radiusAtMostOne (grid : ℕ) : 1 / (grid + 1 : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (grid + 1 : ℝ))).mpr
    have nonnegative : (0 : ℝ) ≤ grid := Nat.cast_nonneg _
    linarith
  have approximatingWithin (grid : ℕ) (index : Fin count) : (times (coordinates grid index) : ℝ) ≤ horizon := by
    have closeOne := (close grid index).trans_le (radiusAtMostOne grid)
    rw [NNReal.dist_eq, abs_lt] at closeOne
    linarith [within index]
  have coordinateConverges (index : Fin count) : Tendsto (fun grid => times (coordinates grid index)) atTop (𝓝 (futureTimes index)) := by
    apply Metric.tendsto_nhds.mpr
    intro tolerance positive
    filter_upwards [meshConvergence.eventually (gt_mem_nhds positive)] with grid small
    have bound : dist (times (coordinates grid index)) (futureTimes index) <
        1 / (grid + 1 : ℝ) := by
      simpa only [dist_comm] using close grid index
    exact bound.trans small
  let laws := fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)
  let sample := fun path : ℕ → Space => fun index : Fin count => countableTimeContinuousSampleCompletion times dense path (futureTimes index)
  let reconstruction := fun grid (path : ℕ → Space) => fun index : Fin count =>
    countableTimeContinuousSampleCompletion times dense path (times (coordinates grid index))
  let reconstructions := fun grid depth => finiteFlooredTimeSampleCompletion (scales depth)
    (fun index => times (coordinates grid index)) (placement depth)
  have sampleMeasurable : Measurable sample := measurable_pi_lambda _ fun index =>
    countableTimeContinuousSample_evaluation_measurable_completion times dense (futureTimes index)
  have reconstructionMeasurable (grid : ℕ) : Measurable (reconstruction grid) := measurable_pi_lambda _ fun index =>
    countableTimeContinuousSample_evaluation_measurable_completion times dense (times (coordinates grid index))
  have reconstructionConverges (path : ℕ → Space) : Tendsto (fun grid => reconstruction grid path) atTop (𝓝 (sample path)) := by
    apply tendsto_pi_nhds.mpr
    intro index
    exact (countableTimeContinuousSample_continuous_completion times dense path).continuousAt.tendsto.comp (coordinateConverges index)
  have inMeasure := tendstoInMeasure_of_tendsto_ae (μ := (limitLaw : Measure (ℕ → Space)))
    (fun grid => (reconstructionMeasurable grid).aestronglyMeasurable) (Eventually.of_forall reconstructionConverges)
  have limitApproximation := tendstoInMeasure_iff_measureReal_dist.mp inMeasure
  apply probability_sample_weak_of_reconstructions_completion laws (limitLaw : Measure (ℕ → Space))
    (fun depth => finiteFlooredTimeSampleCompletion (scales depth) futureTimes (placement depth)) sample
    (fun depth => finiteFlooredTimeSample_measurable_completion _ _ _) sampleMeasurable
    reconstructions reconstruction (fun grid depth => finiteFlooredTimeSample_measurable_completion _ _ _)
    reconstructionMeasurable
  · intro grid
    have mapped := countableTimeLaws_finite_marginals_completion _ limitLaw weak (coordinates grid)
    have limitIdentity : limitLaw.map (reconstructionMeasurable grid).aemeasurable =
        limitLaw.map (show AEMeasurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates grid index)) (limitLaw : Measure (ℕ → Space)) from
          (by fun_prop : Measurable _).aemeasurable) := by
      apply Subtype.ext
      apply Measure.map_congr
      filter_upwards [countableTimeContinuousSample_ae_agreement_completion times dense limitLaw regular] with path agreement
      funext index
      exact agreement (coordinates grid index)
    rw [← limitIdentity] at mapped
    apply mapped.congr'
    apply Eventually.of_forall
    intro depth
    apply Subtype.ext
    change ((laws depth).map (discreteRescaledObservationCompletion (scales depth) times (placement depth))).map
      (fun path : ℕ → Space => fun index : Fin count => path (coordinates grid index)) =
        (laws depth).map (reconstructions grid depth)
    rw [Measure.map_map (by fun_prop : Measurable (fun path : ℕ → Space => fun index : Fin count => path (coordinates grid index)))
      (discreteRescaledObservation_measurable_completion _ _ _)]
    rfl
  · intro tolerance error tolerancePositive errorPositive
    obtain ⟨duration, durationPositive, finiteProbabilities⟩ := chainModulus tolerance error tolerancePositive errorPositive
    have limitProbabilities := (limitApproximation tolerance tolerancePositive).eventually (gt_mem_nhds errorPositive)
    obtain ⟨grid, mesh, limitProbability⟩ := ((meshConvergence.eventually (gt_mem_nhds durationPositive)).and limitProbabilities).exists
    refine ⟨grid, ?_, ?_⟩
    · filter_upwards [finiteProbabilities] with depth probability
      refine ⟨finiteIntervalChainBadModulusCompletion (placement depth) (scales depth) horizon duration tolerance,
        finiteIntervalChainBadModulus_measurable_completion _ (measurable_of_finite _) _ _ _ _, probability, ?_⟩
      intro path good
      apply (dist_pi_le_iff tolerancePositive.le).mpr
      intro index
      exact finiteChain_good_realTime_modulus_completion _ _ _ _ _ (scaleNonnegative depth) path good
        (futureTimes index) (times (coordinates grid index)) (by linarith [within index])
        (approximatingWithin grid index) ((close grid index).trans mesh)
    · refine ⟨{path | tolerance ≤ dist (reconstruction grid path) (sample path)},
        measurableSet_le measurable_const ((reconstructionMeasurable grid).dist sampleMeasurable), limitProbability.le, ?_⟩
      intro path good
      have bound : dist (reconstruction grid path) (sample path) < tolerance :=
        lt_of_not_ge good
      simpa only [dist_comm] using bound.le

end
end IGSIII34.Diffusion


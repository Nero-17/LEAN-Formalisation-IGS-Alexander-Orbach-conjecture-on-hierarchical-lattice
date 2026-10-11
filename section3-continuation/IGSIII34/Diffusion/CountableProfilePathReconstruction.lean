import IGSIII34.Diffusion.CountableDistanceProfile
import IGSIII34.Diffusion.CountablePathMeasurableExtensionCompletion20261011
import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion20261011
import IGSIII34.Diffusion.UsualLocalJ1PathLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

variable {Labels : Type*} [Countable Labels]

/-- Measurable reconstruction into the genuine full càdlàg carrier. On the
measurable set of locally uniformly continuous skeletons it is the unique
continuous extension; elsewhere it is a constant continuous path. -/
def countableProfileCadlagReconstruction (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    (ℕ → CountableDistanceProfile Labels) →
      SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile Labels) :=
  continuousCadlagSampleCompletion20261011
    (countableTimeContinuousSampleCompletion20261011 times dense)
    (countableTimeContinuousSample_continuous_completion20261011 times dense)

theorem countableProfileCadlagReconstruction_measurable
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableProfileCadlagReconstruction (Labels := Labels) times dense) :=
  continuousCadlagSample_measurable_completion20261011
    (countableTimeContinuousSampleCompletion20261011 times dense)
    (countableTimeContinuousSample_continuous_completion20261011 times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)

theorem countableProfileCadlagReconstruction_continuous_path
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (path : ℕ → CountableDistanceProfile Labels) :
    Continuous (fun time => (countableProfileCadlagReconstruction times dense path).val time) :=
  countableTimeContinuousSample_continuous_completion20261011 times dense path

theorem countableProfileCadlagReconstruction_observation
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (path : ℕ → CountableDistanceProfile Labels)
    (regular : countableTimeLocalUniformContinuityCompletion20261011 times path)
    (coordinate : ℕ) :
    (countableProfileCadlagReconstruction times dense path).val (times coordinate) = path coordinate := by
  classical
  change countableTimeContinuousSampleCompletion20261011 times dense path (times coordinate) = _
  rw [countableTimeContinuousSampleCompletion20261011, if_pos regular]
  exact (countableTimeContinuousExtension_properties_completion20261011 times dense path regular).2 coordinate

theorem countableProfileContinuous_observation_regular
    (times : ℕ → ℝ≥0) (sample : ℝ≥0 → CountableDistanceProfile Labels)
    (continuous : Continuous sample) :
    countableTimeLocalUniformContinuityCompletion20261011 times (fun index => sample (times index)) := by
  intro horizon tolerance positive
  have uniform := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) horizon)).uniformContinuousOn_of_continuous
    continuous.continuousOn
  obtain ⟨duration, durationPositive, close⟩ := Metric.uniformContinuousOn_iff.mp uniform tolerance positive
  refine ⟨duration, durationPositive, ?_⟩
  intro first last firstBefore lastBefore near
  exact close (times first) ⟨zero_le, by exact_mod_cast firstBefore⟩
    (times last) ⟨zero_le, by exact_mod_cast lastBefore⟩ near

/-- Observing and reconstructing a continuous path preserves its value at
every nonnegative real time, rather than only at the observed coordinates. -/
theorem countableProfileCadlagReconstruction_continuous_identity
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (sample : ℝ≥0 → CountableDistanceProfile Labels) (continuous : Continuous sample) :
    countableProfileCadlagReconstruction times dense (fun index => sample (times index)) =
      (⟨⟨sample⟩, continuous_path_cadlag_completion20261011 sample continuous⟩ :
        SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile Labels)) := by
  apply Subtype.ext
  apply congrArg SkorokhodGlobalPathCompletion20261011.mk
  apply dense.equalizer (countableProfileCadlagReconstruction_continuous_path times dense _) continuous
  funext coordinate
  exact countableProfileCadlagReconstruction_observation times dense _
    (countableProfileContinuous_observation_regular times sample continuous) coordinate

theorem countableProfileCadlagReconstruction_probability_identity
    {Outcome : Type*} [MeasurableSpace Outcome]
    (times : ℕ → ℝ≥0) (dense : DenseRange times) (law : ProbabilityMeasure Outcome)
    (sample : Outcome → ℝ≥0 → CountableDistanceProfile Labels)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    (law.map ((measurable_pi_lambda _ (fun index => evaluations (times index))).aemeasurable)).map
      (countableProfileCadlagReconstruction_measurable times dense).aemeasurable =
      continuousCadlagProbabilityCompletion20261011 law sample continuous evaluations := by
  apply Subtype.ext
  change ((law : Measure Outcome).map (fun outcome index => sample outcome (times index))).map
    (countableProfileCadlagReconstruction times dense) =
      (law : Measure Outcome).map (continuousCadlagSampleCompletion20261011 sample continuous)
  rw [Measure.map_map (countableProfileCadlagReconstruction_measurable times dense)
    (measurable_pi_lambda _ (fun index => evaluations (times index)))]
  congr 1
  funext outcome
  exact countableProfileCadlagReconstruction_continuous_identity times dense (sample outcome) (continuous outcome)

/-- Side coordinates such as genuine metric-space geometry and both mass
laws are retained exactly while reconstructing every path time. -/
def countableProfileJointReconstruction {Side : Type*}
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    (Side × (ℕ → CountableDistanceProfile Labels)) →
      Side × SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile Labels) :=
  fun pair => (pair.1, countableProfileCadlagReconstruction times dense pair.2)

theorem countableProfileJointReconstruction_measurable {Side : Type*} [MeasurableSpace Side]
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableProfileJointReconstruction (Side := Side) (Labels := Labels) times dense) :=
  measurable_fst.prodMk ((countableProfileCadlagReconstruction_measurable times dense).comp measurable_snd)

def countableProfileUsualLocalJointReconstruction {Side : Type*}
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    (Side × (ℕ → CountableDistanceProfile Labels)) →
      Side × UsualLocalJ1Path (CountableDistanceProfile Labels) :=
  fun pair => (pair.1, integerJ1ToUsualLocalJ1Path (countableProfileCadlagReconstruction times dense pair.2))

theorem countableProfileUsualLocalJointReconstruction_measurable
    {Side : Type*} [MeasurableSpace Side]
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableProfileUsualLocalJointReconstruction (Side := Side) (Labels := Labels) times dense) :=
  measurable_fst.prodMk
    ((integerJ1ToUsualLocalJ1Path_continuous.measurable.comp
      (countableProfileCadlagReconstruction_measurable times dense)).comp measurable_snd)

end
end IGSIII34.Diffusion

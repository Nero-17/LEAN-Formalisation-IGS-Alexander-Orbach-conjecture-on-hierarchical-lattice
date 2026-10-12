import IGSIII34.Diffusion.SkorokhodGlobalContinuousLimitCompletion
import IGSIII34.Diffusion.SkorokhodCadlagWeakCompletion
import IGSIII34.Diffusion.AEContinuousWeakMappingCompletion
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction

/-- Weak convergence tests bounded measurable functions that are continuous
almost everywhere for the limit. The proof maps into the compact interval
containing the test's range, and then tests the continuous coordinate map. -/
theorem probability_weak_integral_bounded_ae_continuous
    {First : Type*} [PseudoMetricSpace First] [MeasurableSpace First] [BorelSpace First]
    (laws : ℕ → ProbabilityMeasure First) (law : ProbabilityMeasure First)
    (weak : Tendsto laws atTop (𝓝 law)) (test : First → ℝ)
    (measurable : Measurable test) (bound : ℝ) (bounded : ∀ point, |test point| ≤ bound)
    (continuous : ∀ᵐ point ∂(law : Measure First), ContinuousAt test point) :
    Tendsto (fun index => ∫ point, test point ∂(laws index : Measure First)) atTop
      (𝓝 (∫ point, test point ∂(law : Measure First))) := by
  let rangeTest : First → Set.Icc (-bound) bound :=
    fun point => ⟨test point, abs_le.mp (bounded point)⟩
  have rangeMeasurable : Measurable rangeTest := measurable.subtype_mk
  have rangeContinuous : ∀ᵐ point ∂(law : Measure First), ContinuousAt rangeTest point := by
    filter_upwards [continuous] with point continuity
    exact continuity.codRestrict _
  have mappedWeak := probability_weak_map_of_ae_continuous_completion
    laws law weak rangeTest (fun _ => rangeMeasurable.aemeasurable)
    rangeMeasurable.aemeasurable rangeContinuous
  let coordinate : Set.Icc (-bound) bound →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨Subtype.val, continuous_subtype_val⟩
  have integrals := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp mappedWeak coordinate
  have identity (measure : ProbabilityMeasure First) :
      (∫ point, coordinate point ∂(measure.map rangeMeasurable.aemeasurable : Measure (Set.Icc (-bound) bound))) =
        ∫ point, test point ∂(measure : Measure First) := by
    change (∫ point, coordinate point ∂(measure : Measure First).map rangeTest) = _
    rw [integral_map rangeMeasurable.aemeasurable
      coordinate.continuous.aestronglyMeasurable]
    rfl
  simpa only [identity] using integrals

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

/-- The standard usual-local J1 sequential test criterion: restriction to
each finite horizon at which the limiting path is continuous converges in
the genuine interval J1 topology. This does not rename integer-horizon J1. -/
def usualLocalJ1SequentiallyContinuousTest
    (test : SkorokhodCadlagPathCompletion Space → ℝ) : Prop :=
  ∀ path : SkorokhodCadlagPathCompletion Space,
  ∀ paths : ℕ → SkorokhodCadlagPathCompletion Space,
    (∀ horizon : ℝ≥0, ContinuousAt path.val.toFun horizon →
      Tendsto (fun index => skorokhodHorizonRestrictionCompletion horizon (paths index).val)
        atTop (𝓝 (skorokhodHorizonRestrictionCompletion horizon path.val))) →
    Tendsto (fun index => test (paths index)) atTop (𝓝 (test path))

/-- The bounded measurable test formulation of usual-local J1 weak
convergence, with its finite-horizon sequential continuity criterion. -/
def usualLocalJ1WeakTestConvergence
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Space)) : Prop :=
  ∀ test : SkorokhodCadlagPathCompletion Space → ℝ,
    Measurable test → ∀ bound : ℝ, (∀ path, |test path| ≤ bound) →
    usualLocalJ1SequentiallyContinuousTest test →
    Tendsto (fun index => ∫ path, test path ∂(laws index : Measure (SkorokhodCadlagPathCompletion Space)))
      atTop (𝓝 (∫ path, test path ∂(law : Measure (SkorokhodCadlagPathCompletion Space))))

/-- A usual-local J1 test is continuous in the integer-horizon carrier at
every continuous limiting path. This is the precise bridge needed for
weak convergence when the limit has continuous sample paths. -/
theorem usualLocalJ1Test_continuousAt_continuous_path
    (test : SkorokhodCadlagPathCompletion Space → ℝ)
    (localContinuous : usualLocalJ1SequentiallyContinuousTest test)
    (path : SkorokhodCadlagPathCompletion Space)
    (pathContinuous : Continuous path.val.toFun) : ContinuousAt test path := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro paths convergence
  apply localContinuous path paths
  intro horizon _
  exact skorokhodGlobal_continuous_limit_all_horizons_completion
    (fun index => (paths index).val) path.val.toFun pathContinuous
    (continuous_subtype_val.tendsto path |>.comp convergence) horizon

/-- Integer-horizon J1 weak convergence to a continuous-path law entails
convergence of every bounded measurable usual-local J1 test. Thus the
paper's local-J1 weak tests follow from the proved stronger carrier result. -/
theorem skorokhodCadlag_weak_usualLocalJ1_test
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (weak : Tendsto laws atTop (𝓝 law))
    (continuousPaths : ∀ᵐ path ∂(law : Measure (SkorokhodCadlagPathCompletion Space)),
      Continuous path.val.toFun)
    (test : SkorokhodCadlagPathCompletion Space → ℝ)
    (measurable : Measurable test) (bound : ℝ) (bounded : ∀ path, |test path| ≤ bound)
    (localContinuous : usualLocalJ1SequentiallyContinuousTest test) :
    Tendsto (fun index => ∫ path, test path ∂(laws index : Measure (SkorokhodCadlagPathCompletion Space)))
      atTop (𝓝 (∫ path, test path ∂(law : Measure (SkorokhodCadlagPathCompletion Space)))) := by
  apply probability_weak_integral_bounded_ae_continuous laws law weak test measurable bound bounded
  filter_upwards [continuousPaths] with path continuity
  exact usualLocalJ1Test_continuousAt_continuous_path test localContinuous path continuity

/-- The direct weak-test entrance for an actually constructed continuous
sample law. Continuity is needed only on that law's image. No measurability
of the set of all continuous paths is required. -/
theorem skorokhodCadlag_weak_usualLocalJ1_test_continuousSample
    [MeasurableSpace Space] [BorelSpace Space]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (weak : Tendsto laws atTop
      (𝓝 (continuousCadlagProbabilityCompletion law sample continuous evaluations)))
    (test : SkorokhodCadlagPathCompletion Space → ℝ)
    (measurable : Measurable test) (bound : ℝ) (bounded : ∀ path, |test path| ≤ bound)
    (localContinuous : usualLocalJ1SequentiallyContinuousTest test) :
    Tendsto (fun index => ∫ path, test path ∂(laws index : Measure (SkorokhodCadlagPathCompletion Space)))
      atTop (𝓝 (∫ path, test path ∂(continuousCadlagProbabilityCompletion law sample continuous evaluations :
        Measure (SkorokhodCadlagPathCompletion Space)))) := by
  apply probability_weak_integral_bounded_ae_continuous laws _ weak test measurable bound bounded
  change ∀ᵐ path ∂(law : Measure Outcome).map (continuousCadlagSampleCompletion sample continuous),
    ContinuousAt test path
  rw [ae_map_iff (continuousCadlagSample_measurable_completion sample continuous evaluations).aemeasurable
    (measurableSet_of_continuousAt test)]
  exact Eventually.of_forall (fun outcome =>
    usualLocalJ1Test_continuousAt_continuous_path test localContinuous
      (continuousCadlagSampleCompletion sample continuous outcome) (continuous outcome))

theorem skorokhodCadlag_weak_usualLocalJ1_tests_continuousSample
    [MeasurableSpace Space] [BorelSpace Space]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion Space))
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (weak : Tendsto laws atTop
      (𝓝 (continuousCadlagProbabilityCompletion law sample continuous evaluations))) :
    usualLocalJ1WeakTestConvergence laws
      (continuousCadlagProbabilityCompletion law sample continuous evaluations) := by
  intro test measurable bound bounded localContinuous
  exact skorokhodCadlag_weak_usualLocalJ1_test_continuousSample
    laws law sample continuous evaluations weak test measurable bound bounded localContinuous

end
end IGSIII34.Diffusion


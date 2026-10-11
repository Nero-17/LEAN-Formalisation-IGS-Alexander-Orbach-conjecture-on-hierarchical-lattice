import IGSIII34.Diffusion.IntegerJ1ToUsualLocalJ1

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

/-- The genuine cadlag carrier equipped with the local-J1 sequential
topology, separated from the stronger integer-horizon carrier. -/
structure UsualLocalJ1Path (Space : Type*) [MetricSpace Space] [CompactSpace Space] where
  path : SkorokhodCadlagPathCompletion20261011 Space

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

instance usualLocalJ1PathTopology : TopologicalSpace (UsualLocalJ1Path Space) :=
  TopologicalSpace.induced UsualLocalJ1Path.path usualLocalJ1SequenceTopology

instance usualLocalJ1PathMeasurable : MeasurableSpace (UsualLocalJ1Path Space) := borel _
instance usualLocalJ1PathBorel : BorelSpace (UsualLocalJ1Path Space) := ⟨rfl⟩

def integerJ1ToUsualLocalJ1Path (path : SkorokhodCadlagPathCompletion20261011 Space) :
    UsualLocalJ1Path Space := ⟨path⟩

theorem integerJ1ToUsualLocalJ1Path_continuous :
    Continuous (integerJ1ToUsualLocalJ1Path (Space := Space)) := by
  rw [continuous_induced_rng]
  exact integerJ1_to_usualLocalJ1_identity_continuous

/-- A true probability law on the explicitly constructed local-J1
topological and Borel carrier, preserving the exact underlying cadlag path. -/
def usualLocalJ1PathProbability
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space)) :
    ProbabilityMeasure (UsualLocalJ1Path Space) :=
  law.map integerJ1ToUsualLocalJ1Path_continuous.measurable.aemeasurable

/-- Full weak convergence on the local-J1 topological carrier follows
from the stronger integer-horizon weak convergence. No measurability or
continuity of individual tests is left as a caller hypothesis. -/
theorem integerJ1_weak_to_usualLocalJ1
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Space))
    (weak : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => usualLocalJ1PathProbability (laws index)) atTop
      (𝓝 (usualLocalJ1PathProbability law)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law weak
    integerJ1ToUsualLocalJ1Path_continuous

end
end IGSIII34.Diffusion

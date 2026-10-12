import IGSIII34.Diffusion.UsualLocalJ1SequenceTopology

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set
open scoped Topology
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

/-- The standard local-J1 window criterion is preserved by every
subsequence tending to infinity. -/
theorem usualLocalJ1Sequence_subsequence
    (paths : ℕ → SkorokhodCadlagPathCompletion Space)
    (path : SkorokhodCadlagPathCompletion Space)
    (convergence : usualLocalJ1SequenceConvergence paths path)
    (selection : ℕ → ℕ) (divergence : Tendsto selection atTop atTop) :
    usualLocalJ1SequenceConvergence (paths ∘ selection) path := by
  intro horizon endpoint
  exact (convergence horizon endpoint).comp divergence

/-- The topology constructed from the usual-local J1 window criterion
is a sequential space. This follows from subsequence extraction, not
from an assumed metrization of the path carrier. -/
theorem usualLocalJ1SequenceTopology_sequential :
    @SequentialSpace (SkorokhodCadlagPathCompletion Space)
      usualLocalJ1SequenceTopology := by
  letI : TopologicalSpace (SkorokhodCadlagPathCompletion Space) := usualLocalJ1SequenceTopology
  constructor
  intro set sequentiallyClosed
  apply isOpen_compl_iff.mp
  intro paths path convergence outside
  by_contra failure
  obtain ⟨selection, increasing, selected⟩ := extraction_of_frequently_atTop (not_eventually.mp failure)
  have subsequence := usualLocalJ1Sequence_subsequence paths path convergence selection increasing.tendsto_atTop
  have selectedConvergence := usualLocalJ1Sequence_tendsto (paths ∘ selection) path subsequence
  apply outside
  apply sequentiallyClosed _ selectedConvergence
  intro index
  simpa only [Function.comp_def, mem_compl_iff, not_not] using selected index

end
end IGSIII34.Diffusion

import IGSIII34.Diffusion.CountableDistanceProfile
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.DenseEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Set
open scoped Topology

variable {Labels Space : Type*} [Countable Labels] [MetricSpace Space]

/-- Every distance to every dense birth point is retained, so the compact
profile identifies the original spatial point exactly. -/
theorem distanceProfilePoint_injective (births : Labels → Space) (dense : DenseRange births) :
    Function.Injective (distanceProfilePoint births) := by
  intro first last equality
  have distances : (fun point => dist first point) = (fun point => dist last point) := by
    apply dense.equalizer (continuous_const.dist continuous_id) (continuous_const.dist continuous_id)
    funext label
    have coordinate := congrArg (fun profile : CountableDistanceProfile Labels => (profile label : ℝ)) equality
    change Real.exp (-dist first (births label)) = Real.exp (-dist last (births label)) at coordinate
    exact neg_injective (Real.exp_injective coordinate)
  have zero := congrFun distances first
  rw [dist_self] at zero
  exact (dist_eq_zero.mp zero.symm).symm

variable [CompactSpace Space]

theorem distanceProfilePoint_isClosedEmbedding (births : Labels → Space) (dense : DenseRange births) :
    Topology.IsClosedEmbedding (distanceProfilePoint births) :=
  (distanceProfilePoint_continuous births).isClosedEmbedding (distanceProfilePoint_injective births dense)

/-- The profile is a homeomorphism onto its closed image. This theorem
does not assert equality with the original metric. -/
def distanceProfileHomeomorph (births : Labels → Space) (dense : DenseRange births) :
    Space ≃ₜ range (distanceProfilePoint births) :=
  (distanceProfilePoint_isClosedEmbedding births dense).isEmbedding.toHomeomorph

theorem distanceProfilePoint_closed_range (births : Labels → Space) (dense : DenseRange births) :
    IsClosed (range (distanceProfilePoint births)) :=
  (distanceProfilePoint_isClosedEmbedding births dense).isClosed_range

end
end IGSIII34.Diffusion

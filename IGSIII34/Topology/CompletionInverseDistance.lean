import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Antilipschitz

set_option autoImplicit false
namespace IGSIII34.Topology
open UniformSpace
open scoped NNReal
noncomputable section

/-- A uniform inverse metric bound on the dense skeleton survives completion. -/
theorem completion_antilipschitz_of_skeleton_bound
    {Skeleton Target : Type*} [MetricSpace Skeleton] [MetricSpace Target]
    (mapping : Completion Skeleton → Target) (continuous : Continuous mapping)
    (constant : ℝ≥0)
    (bound : ∀ first last : Skeleton,
      dist first last ≤ constant * dist (mapping first) (mapping last)) :
    AntilipschitzWith constant mapping := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first last
  refine Completion.induction_on₂ first last
    (isClosed_le (continuous_fst.dist continuous_snd)
      (continuous_const.mul ((continuous.comp continuous_fst).dist
        (continuous.comp continuous_snd)))) ?_
  intro first last
  simpa only [Completion.dist_eq] using bound first last

theorem completion_injective_of_skeleton_bound
    {Skeleton Target : Type*} [MetricSpace Skeleton] [MetricSpace Target]
    (mapping : Completion Skeleton → Target) (continuous : Continuous mapping)
    (constant : ℝ≥0)
    (bound : ∀ first last : Skeleton,
      dist first last ≤ constant * dist (mapping first) (mapping last)) :
    Function.Injective mapping :=
  (completion_antilipschitz_of_skeleton_bound mapping continuous constant bound).injective

end
end IGSIII34.Topology

import IGSIII34.Diffusion.CoerciveObjectiveCompletion20261011

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology

variable {Energy : Type*} [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy]

theorem coerciveObjective_continuous_completion20261011
    (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ) (forcing : StrongDual ℝ Energy) :
    Continuous (coerciveObjectiveCompletion20261011 bilinear forcing) := by
  exact (bilinear.continuous.clm_apply continuous_id).sub (continuous_const.mul forcing.continuous)

theorem coerciveObjective_comparison_of_approximation_completion20261011
    (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ) (forcing : StrongDual ℝ Energy)
    (candidate target : Energy) (approximations : ℕ → Energy)
    (converges : Tendsto approximations atTop (𝓝 target))
    (comparison : ∀ depth, coerciveObjectiveCompletion20261011 bilinear forcing candidate ≤
      coerciveObjectiveCompletion20261011 bilinear forcing (approximations depth)) :
    coerciveObjectiveCompletion20261011 bilinear forcing candidate ≤
      coerciveObjectiveCompletion20261011 bilinear forcing target := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    ((coerciveObjective_continuous_completion20261011 bilinear forcing).tendsto target |>.comp converges)
    (Eventually.of_forall comparison)

end
end IGSIII34.Diffusion

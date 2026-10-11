import IGSIII34.Diffusion.OriginalJointCoupledUsualJ1
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology NNReal PiCountable

theorem originalJointCoupledUsualJ1_continuous_limit_cost
    (sequence : ℕ → OriginalJointCompactRepresentative)
    (limit : OriginalJointCompactRepresentative)
    (couplings : ∀ index, OriginalJointCompactCoupling (sequence index) limit)
    (convergence : OriginalJointCoupledUsualJ1Convergence sequence limit couplings)
    (limitContinuous : Continuous limit.path.val.toFun) :
    Tendsto (fun index => (couplings index).cost) atTop (𝓝 0) := by
  have coordinateConvergence (horizon : ℕ) :
      Tendsto (fun index => min (2⁻¹ ^ Encodable.encode horizon)
        ((couplings index).horizonPathDistance (horizon + 1))) atTop (𝓝 (0 : ℝ)) := by
    have coordinate := convergence.2 (horizon + 1) (limitContinuous.continuousAt)
    have clipped := (tendsto_const_nhds (x := (2⁻¹ : ℝ) ^ Encodable.encode horizon)).min coordinate
    have nonnegative : 0 ≤ (2⁻¹ : ℝ) ^ Encodable.encode horizon := by positivity
    simpa only [min_eq_right nonnegative] using clipped
  have domination : ∀ᶠ index in atTop, ∀ horizon : ℕ,
      ‖min (2⁻¹ ^ Encodable.encode horizon) ((couplings index).horizonPathDistance (horizon + 1))‖ ≤
      (1 / 2 : ℝ) ^ Encodable.encode horizon := by
    filter_upwards [] with index horizon
    have nonnegative : 0 ≤ (couplings index).horizonPathDistance (horizon + 1) := dist_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) nonnegative)]
    simpa only [one_div] using min_le_left (2⁻¹ ^ Encodable.encode horizon)
      ((couplings index).horizonPathDistance (horizon + 1))
  have pathConvergence := tendsto_tsum_of_dominated_convergence
    (summable_geometric_two_encode (ι := ℕ)) coordinateConvergence domination
  simp only [tsum_zero] at pathConvergence
  have wholeConvergence : Tendsto (fun index => dist
      (skorokhodGlobalCarrierMapCompletion20261011 (couplings index).firstPlacement (sequence index).path.val)
      (skorokhodGlobalCarrierMapCompletion20261011 (couplings index).lastPlacement limit.path.val)) atTop (𝓝 0) := by
    exact pathConvergence
  have total := convergence.1.add wholeConvergence
  simp only [add_zero] at total
  convert total using 1
  funext index
  rfl

theorem originalJointCompactClass_tendsto_iff_coupled_usualJ1_continuous_limit
    (sequence : ℕ → OriginalJointCompactRepresentative)
    (limit : OriginalJointCompactRepresentative)
    (limitContinuous : Continuous limit.path.val.toFun) :
    Tendsto (fun index => originalJointCompactClass (sequence index)) atTop
      (𝓝 (originalJointCompactClass limit)) ↔
    ∃ couplings : ∀ index, OriginalJointCompactCoupling (sequence index) limit,
      OriginalJointCoupledUsualJ1Convergence sequence limit couplings := by
  constructor
  · exact fun convergence => originalJointCompactClass_tendsto_coupled_usualJ1
      sequence limit convergence limitContinuous
  · rintro ⟨couplings, convergence⟩
    have costConvergence := originalJointCoupledUsualJ1_continuous_limit_cost
      sequence limit couplings convergence limitContinuous
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun index => dist_nonneg)
      (fun index => originalJointCompactDistance_le_cost (couplings index))
      costConvergence

end
end IGSIII34.Diffusion

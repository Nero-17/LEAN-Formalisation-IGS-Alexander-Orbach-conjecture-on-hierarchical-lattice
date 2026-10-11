import IGSIII34.Diffusion.OriginalJointCompactCoupling
import IGSIII34.Diffusion.OriginalMetricContinuousLimitTransport
import IGSIII34.Diffusion.OriginalJointCompactDistance
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology NNReal

def OriginalJointCompactCoupling.geometryCost
    {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) : ℝ :=
  jointMeasuredMarkedStateCost
    (jointMeasuredMarkedStateMap coupling.firstPlacement coupling.firstIsometry.continuous
      (originalJointRepresentativeState first))
    (jointMeasuredMarkedStateMap coupling.lastPlacement coupling.lastIsometry.continuous
      (originalJointRepresentativeState last))

def OriginalJointCompactCoupling.horizonPathDistance
    {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) (horizon : ℝ≥0) : ℝ :=
  dist (skorokhodHorizonRestrictionCompletion20261011 horizon
      (skorokhodGlobalCarrierMapCompletion20261011 coupling.firstPlacement first.path.val))
    (skorokhodHorizonRestrictionCompletion20261011 horizon
      (skorokhodGlobalCarrierMapCompletion20261011 coupling.lastPlacement last.path.val))

/-- This criterion explicitly uses the original carrier metric, physical
probability masses, planted marks and genuine J1 restrictions of the whole
paths after true isometric placement. It is a coupling criterion, rather
than a renaming of the stronger integer-horizon metric. -/
def OriginalJointCoupledUsualJ1Convergence
    (sequence : ℕ → OriginalJointCompactRepresentative)
    (limit : OriginalJointCompactRepresentative)
    (couplings : ∀ index, OriginalJointCompactCoupling (sequence index) limit) : Prop :=
  Tendsto (fun index => (couplings index).geometryCost) atTop (𝓝 0) ∧
    ∀ horizon : ℝ≥0, ContinuousAt limit.path.val.toFun horizon →
      Tendsto (fun index => (couplings index).horizonPathDistance horizon) atTop (𝓝 0)

theorem originalJointCoupledUsualJ1_of_integer_cost_continuous_limit
    (sequence : ℕ → OriginalJointCompactRepresentative)
    (limit : OriginalJointCompactRepresentative)
    (couplings : ∀ index, OriginalJointCompactCoupling (sequence index) limit)
    (convergence : Tendsto (fun index => (couplings index).cost) atTop (𝓝 0))
    (limitContinuous : Continuous limit.path.val.toFun) :
    OriginalJointCoupledUsualJ1Convergence sequence limit couplings := by
  have geometryNonnegative (index : ℕ) : 0 ≤ (couplings index).geometryCost := by
    unfold OriginalJointCompactCoupling.geometryCost jointMeasuredMarkedStateCost
    exact add_nonneg (add_nonneg dist_nonneg (Finset.sum_nonneg fun _ _ => dist_nonneg))
      (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
  have geometryBound (index : ℕ) : (couplings index).geometryCost ≤ (couplings index).cost := by
    exact le_add_of_nonneg_right dist_nonneg
  constructor
  · exact squeeze_zero geometryNonnegative geometryBound convergence
  · intro horizon _
    apply Metric.tendsto_nhds.mpr
    intro tolerance tolerancePositive
    obtain ⟨error, errorPositive, close⟩ := skorokhodGlobal_near_isometric_continuous_horizon
      limit.path.val.toFun limitContinuous horizon tolerance tolerancePositive
    filter_upwards [convergence.eventually (gt_mem_nhds errorPositive)] with index small
    rw [Real.dist_eq, sub_zero]
    unfold OriginalJointCompactCoupling.horizonPathDistance
    rw [abs_of_nonneg dist_nonneg]
    apply close (couplings index).ambient (couplings index).lastPlacement
      (couplings index).lastIsometry
      (skorokhodGlobalCarrierMapCompletion20261011 (couplings index).firstPlacement (sequence index).path.val)
    have pathBound : dist
        (skorokhodGlobalCarrierMapCompletion20261011 (couplings index).firstPlacement (sequence index).path.val)
        (skorokhodGlobalCarrierMapCompletion20261011 (couplings index).lastPlacement limit.path.val) ≤
        (couplings index).cost := by
      exact le_add_of_nonneg_left (geometryNonnegative index)
    exact pathBound.trans_lt small

/-- Metric convergence supplies actual couplings for the original usual
J1 restriction criterion whenever the limiting original path is continuous. -/
theorem originalJointCompactClass_tendsto_coupled_usualJ1
    (sequence : ℕ → OriginalJointCompactRepresentative)
    (limit : OriginalJointCompactRepresentative)
    (convergence : Tendsto (fun index => originalJointCompactClass (sequence index)) atTop
      (𝓝 (originalJointCompactClass limit)))
    (limitContinuous : Continuous limit.path.val.toFun) :
    ∃ couplings : ∀ index, OriginalJointCompactCoupling (sequence index) limit,
      OriginalJointCoupledUsualJ1Convergence sequence limit couplings := by
  have existence (index : ℕ) : ∃ coupling : OriginalJointCompactCoupling (sequence index) limit,
      coupling.cost < originalJointCompactDistance (sequence index) limit + 1 / ((index : ℝ) + 1) := by
    apply (originalJointCompactDistance_lt_iff _ _ _).mp
    have positive : 0 < 1 / ((index : ℝ) + 1) := by positivity
    linarith
  choose couplings bounds using existence
  have distanceConvergence : Tendsto (fun index => originalJointCompactDistance (sequence index) limit)
      atTop (𝓝 0) := by
    simpa only [originalJointCompactClass_dist] using tendsto_iff_dist_tendsto_zero.mp convergence
  have upperConvergence : Tendsto (fun index =>
      originalJointCompactDistance (sequence index) limit + 1 / ((index : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_zero] using distanceConvergence.add tendsto_one_div_add_atTop_nhds_zero_nat
  have costConvergence := squeeze_zero (fun index => (couplings index).cost_nonnegative)
    (fun index => (bounds index).le) upperConvergence
  exact ⟨couplings, originalJointCoupledUsualJ1_of_integer_cost_continuous_limit
    sequence limit couplings costConvergence limitContinuous⟩

end
end IGSIII34.Diffusion

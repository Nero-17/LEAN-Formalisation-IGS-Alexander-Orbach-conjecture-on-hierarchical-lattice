import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def skorokhodHorizonRestrictionCompletion (horizon : ℝ≥0)
    (path : SkorokhodGlobalPathCompletion Space) : SkorokhodIntervalPathCompletion Space :=
  ⟨fun time => path (horizon * ⟨time.val, time.property.1⟩)⟩

/-- At a continuous limit, genuine integer-horizon J1 convergence gives
uniform convergence on every bounded physical-time interval. -/
theorem skorokhodGlobal_continuous_limit_uniform_completion
    {Index : Type*} {along : Filter Index}
    (paths : Index → SkorokhodGlobalPathCompletion Space)
    (path : ℝ≥0 → Space) (pathContinuous : Continuous path)
    (convergence : Tendsto paths along (𝓝 (⟨path⟩ : SkorokhodGlobalPathCompletion Space)))
    (horizon : ℝ≥0) (tolerance : ℝ) (positive : 0 < tolerance) :
    ∀ᶠ index in along, ∀ time : ℝ≥0, time ≤ horizon → dist (paths index time) (path time) < tolerance := by
  let count : ℕ := ⌊(horizon : ℝ)⌋₊
  let profile : C(SkorokhodIntervalTimeCompletion, Space) :=
    ⟨fun time => path ((count+1 : ℝ≥0) * ⟨time.val, time.property.1⟩), pathContinuous.comp (by fun_prop)⟩
  have profileConvergence := (skorokhodGlobal_tendsto_iff_completion.mp convergence) count
  have uniform := skorokhodJ1_continuous_limit_uniform_completion
    along (fun index => skorokhodIntegerProfileCompletion (paths index) count) profile profileConvergence tolerance positive
  filter_upwards [uniform] with index bound
  intro time before
  have countPositive : 0 < (count+1 : ℝ) := by positivity
  have physicalBefore : (time : ℝ) ≤ (count+1 : ℝ) :=
    (NNReal.coe_le_coe.mpr before).trans (Nat.lt_floor_add_one (horizon : ℝ)).le
  let unitTime : SkorokhodIntervalTimeCompletion :=
    ⟨(time : ℝ) / (count+1 : ℝ),
      ⟨div_nonneg time.property countPositive.le, (div_le_one countPositive).mpr physicalBefore⟩⟩
  have timeIdentity : (count+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩ = time := by
    apply NNReal.eq
    change (count+1 : ℝ) * ((time : ℝ) / (count+1 : ℝ)) = (time : ℝ)
    exact mul_div_cancel₀ _ countPositive.ne'
  have point := bound unitTime
  change dist (paths index ((count+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩))
    (path ((count+1 : ℝ≥0) * ⟨unitTime.val, unitTime.property.1⟩)) < tolerance at point
  rwa [timeIdentity] at point

/-- Consequently every finite-horizon restriction converges in the
genuine time-change J1 topology, including arbitrary noninteger horizons.
This is the standard local-J1 convergence criterion at continuous paths. -/
theorem skorokhodGlobal_continuous_limit_all_horizons_completion
    {Index : Type*} {along : Filter Index}
    (paths : Index → SkorokhodGlobalPathCompletion Space)
    (path : ℝ≥0 → Space) (pathContinuous : Continuous path)
    (convergence : Tendsto paths along (𝓝 (⟨path⟩ : SkorokhodGlobalPathCompletion Space)))
    (horizon : ℝ≥0) :
    Tendsto (fun index => skorokhodHorizonRestrictionCompletion horizon (paths index))
      along (𝓝 (skorokhodHorizonRestrictionCompletion horizon ⟨path⟩)) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [skorokhodGlobal_continuous_limit_uniform_completion paths path pathContinuous
    convergence horizon (tolerance/2) (by positivity)] with index bound
  have edistance : edist (skorokhodHorizonRestrictionCompletion horizon (paths index))
      (skorokhodHorizonRestrictionCompletion horizon ⟨path⟩) ≤ ENNReal.ofReal (tolerance/2) := by
    apply (skorokhodJ1EDist_le_uniform_completion _ _).trans
    apply iSup_le
    intro time
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    apply (bound (horizon * ⟨time.val, time.property.1⟩) ?_).le
    apply NNReal.coe_le_coe.mp
    change (horizon : ℝ) * (time : ℝ) ≤ (horizon : ℝ)
    have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
    have raw := mul_le_mul_of_nonneg_left time.property.2 horizon.property
    rw [realLE] at raw
    rw [mul_one] at raw
    convert raw using 1 <;> rfl
  exact ((edist_le_ofReal (by positivity : 0 ≤ tolerance/2)).mp edistance).trans_lt (by linarith)

end
end IGSIII34.Diffusion

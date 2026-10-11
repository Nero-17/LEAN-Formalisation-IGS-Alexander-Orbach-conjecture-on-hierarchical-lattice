import IGSIII34.Diffusion.SkorokhodEndpointJumpGridCompletion20261011
import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3800000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def skorokhodGlobalMeshSampleCompletion20261011
    (path : ℝ≥0 → Space) (grid : ℕ) : SkorokhodGlobalPathCompletion20261011 Space :=
  skorokhodGlobalFloorReconstructionCompletion20261011 (grid+1 : ℝ)
    (fun index => path ((index : ℝ≥0) / (grid+1 : ℝ≥0)))

theorem skorokhodGlobalMesh_integer_profile_completion20261011
    (path : ℝ≥0 → Space) (grid horizon : ℕ) :
    skorokhodIntegerProfileCompletion20261011 (skorokhodGlobalMeshSampleCompletion20261011 path grid) horizon =
      skorokhodFiniteReconstructionCompletion20261011
        (skorokhodRegularGridSelectionCompletion20261011 ((grid+1)*(horizon+1)-1))
        (fun coordinate => skorokhodIntegerProfileCompletion20261011 (⟨path⟩ : SkorokhodGlobalPathCompletion20261011 Space) horizon
          (skorokhodRegularGridPointCompletion20261011 ((grid+1)*(horizon+1)-1) coordinate)) := by
  have denominator : (grid+1)*(horizon+1)-1+1 = (grid+1)*(horizon+1) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity : 0 < (grid+1)*(horizon+1)))
  apply congrArg SkorokhodIntervalPathCompletion20261011.mk
  funext time
  apply congrArg path
  apply NNReal.eq
  change (⌊(grid+1 : ℝ) * ((horizon+1 : ℝ) * (time : ℝ))⌋₊ : ℝ) / (grid+1 : ℝ) =
    (horizon+1 : ℝ) *
      ((⌊((((grid+1)*(horizon+1)-1 : ℕ) : ℝ) + 1) * (time : ℝ)⌋₊ : ℝ) /
        ((((grid+1)*(horizon+1)-1 : ℕ) : ℝ) + 1))
  have realDenominator : ((((grid+1)*(horizon+1)-1 : ℕ) : ℝ) + 1) = (grid+1 : ℝ) * (horizon+1 : ℝ) := by
    exact_mod_cast denominator
  rw [realDenominator, mul_assoc]
  field_simp

/-- A full-time path with finitely many actual jumps on every compact
interval is the genuine J1 limit of its measurable fixed-mesh samples.
Jumps at integer endpoints are preserved as endpoint values. -/
theorem skorokhodGlobalMesh_tendsto_of_finite_jumps_completion20261011
    (path : ℝ≥0 → Space)
    (finite : ∀ horizon : ℕ, ∃ count : ℕ,
      ∃ knots : Fin count → SkorokhodIntervalTimeCompletion20261011,
        StrictMono knots ∧ (∀ index, 0 < (knots index).val ∧ (knots index).val < 1) ∧
        ∃ states : Fin (count+1) → Space, ∃ endpoint : Space,
          skorokhodIntegerProfileCompletion20261011 (⟨path⟩ : SkorokhodGlobalPathCompletion20261011 Space) horizon =
            finiteEndpointJumpIntervalPathCompletion20261011 knots states endpoint) :
    Tendsto (skorokhodGlobalMeshSampleCompletion20261011 path) atTop
      (𝓝 (⟨path⟩ : SkorokhodGlobalPathCompletion20261011 Space)) := by
  apply skorokhodGlobal_tendsto_iff_completion20261011.mpr
  intro horizon
  obtain ⟨count, knots, increasing, interior, states, endpoint, identity⟩ := finite horizon
  have intervalConvergence := finiteEndpointJump_grid_tendsto_completion20261011 knots increasing interior states endpoint
  rw [← identity] at intervalConvergence
  have meshAtTop : Tendsto (fun grid : ℕ => (grid+1)*(horizon+1)-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro bound
    filter_upwards [eventually_ge_atTop bound] with grid gridBound
    have multiplication : grid+1 ≤ (grid+1)*(horizon+1) := by
      simpa only [mul_one] using Nat.mul_le_mul_left (grid+1) (Nat.le_add_left 1 horizon)
    exact gridBound.trans (by omega)
  have convergence := intervalConvergence.comp meshAtTop
  apply convergence.congr'
  exact Eventually.of_forall (fun grid => (skorokhodGlobalMesh_integer_profile_completion20261011 path grid horizon).symm)

theorem skorokhodGlobal_jump_sample_aemeasurable_completion20261011
    [MeasurableSpace Space] [BorelSpace Space]
    {Outcome : Type*} [MeasurableSpace Outcome] (law : Measure Outcome)
    (sample : Outcome → ℝ≥0 → Space) (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (finite : ∀ᵐ outcome ∂law, ∀ horizon : ℕ, ∃ count : ℕ,
      ∃ knots : Fin count → SkorokhodIntervalTimeCompletion20261011,
        StrictMono knots ∧ (∀ index, 0 < (knots index).val ∧ (knots index).val < 1) ∧
        ∃ states : Fin (count+1) → Space, ∃ endpoint : Space,
          skorokhodIntegerProfileCompletion20261011 (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space) horizon =
            finiteEndpointJumpIntervalPathCompletion20261011 knots states endpoint) :
    AEMeasurable (fun outcome => (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space)) law := by
  apply aemeasurable_of_tendsto_metrizable_ae'
    (f := fun grid outcome => skorokhodGlobalMeshSampleCompletion20261011 (sample outcome) grid)
  · intro grid
    exact ((skorokhodGlobalFloorReconstruction_measurable_completion20261011 (grid+1 : ℝ) (by positivity)).comp
      (measurable_pi_lambda _ (fun index => evaluations ((index : ℝ≥0) / (grid+1 : ℝ≥0))))).aemeasurable
  · exact finite.mono (fun outcome regular => skorokhodGlobalMesh_tendsto_of_finite_jumps_completion20261011 (sample outcome) regular)

end
end IGSIII34.Diffusion

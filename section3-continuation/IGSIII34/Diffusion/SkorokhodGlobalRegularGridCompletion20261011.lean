import IGSIII34.Diffusion.SkorokhodGlobalFiniteGridCompletion20261011
import IGSIII34.Diffusion.SkorokhodRegularGridCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal

def skorokhodGlobalClampedTimeCompletion20261011 (horizon : ℕ) (time : ℝ≥0) :
    SkorokhodIntervalTimeCompletion20261011 :=
  ⟨min ((time : ℝ) / (horizon+1 : ℝ)) 1,
    ⟨le_min (div_nonneg time.property (by positivity)) (by norm_num), min_le_right _ _⟩⟩

def skorokhodGlobalRegularGridSelectionCompletion20261011 (horizon grid : ℕ)
    (time : ℝ≥0) : Fin (grid+2) :=
  skorokhodRegularGridSelectionCompletion20261011 grid
    (skorokhodGlobalClampedTimeCompletion20261011 horizon time)

def skorokhodGlobalRegularGridPointCompletion20261011 (horizon grid : ℕ)
    (index : Fin (grid+2)) : ℝ≥0 :=
  (horizon+1 : ℝ≥0) *
    ⟨(skorokhodRegularGridPointCompletion20261011 grid index : ℝ),
      (skorokhodRegularGridPointCompletion20261011 grid index).property.1⟩

theorem skorokhodGlobalRegularGridPoint_le_completion20261011 (horizon grid : ℕ)
    (index : Fin (grid+2)) : skorokhodGlobalRegularGridPointCompletion20261011 horizon grid index ≤ horizon+1 := by
  apply NNReal.coe_le_coe.mp
  change (horizon+1 : ℝ) * (skorokhodRegularGridPointCompletion20261011 grid index : ℝ) ≤ (horizon+1 : ℝ)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (skorokhodRegularGridPointCompletion20261011 grid index).property.2 (by positivity : 0 ≤ (horizon+1 : ℝ))

theorem skorokhodGlobalRegularGridSelection_near_completion20261011 (horizon grid : ℕ)
    (time : ℝ≥0) (before : time ≤ horizon+1) :
    dist time (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid
      (skorokhodGlobalRegularGridSelectionCompletion20261011 horizon grid time)) <
      (horizon+1 : ℝ) / (grid+1 : ℝ) := by
  have horizonPositive : 0 < (horizon+1 : ℝ) := by positivity
  have clamped : (skorokhodGlobalClampedTimeCompletion20261011 horizon time : ℝ) =
      (time : ℝ) / (horizon+1 : ℝ) := by
    apply min_eq_left
    apply (div_le_one horizonPositive).mpr
    exact_mod_cast before
  have close := skorokhodRegularGridSelection_near_completion20261011 grid
    (skorokhodGlobalClampedTimeCompletion20261011 horizon time)
  have scaled := mul_lt_mul_of_pos_left close horizonPositive
  change |(time : ℝ) - (horizon+1 : ℝ) *
    (skorokhodRegularGridPointCompletion20261011 grid
      (skorokhodGlobalRegularGridSelectionCompletion20261011 horizon grid time) : ℝ)| < _
  change (horizon+1 : ℝ) * |(skorokhodGlobalClampedTimeCompletion20261011 horizon time : ℝ) -
    (skorokhodRegularGridPointCompletion20261011 grid
      (skorokhodGlobalRegularGridSelectionCompletion20261011 horizon grid time) : ℝ)| < _ at scaled
  rw [clamped] at scaled
  have absoluteIdentity : (horizon+1 : ℝ) * |(time : ℝ) / (horizon+1 : ℝ) -
      (skorokhodRegularGridPointCompletion20261011 grid
        (skorokhodGlobalRegularGridSelectionCompletion20261011 horizon grid time) : ℝ)| =
      |(time : ℝ) - (horizon+1 : ℝ) *
        (skorokhodRegularGridPointCompletion20261011 grid
          (skorokhodGlobalRegularGridSelectionCompletion20261011 horizon grid time) : ℝ)| := by
    rw [← abs_of_pos horizonPositive]
    rw [← abs_mul, abs_of_pos horizonPositive, mul_sub, mul_div_cancel₀ _ horizonPositive.ne']
  rw [absoluteIdentity] at scaled
  simpa only [mul_one_div] using scaled

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def skorokhodGlobalRegularReconstructionCompletion20261011 (horizon grid : ℕ)
    (path : SkorokhodGlobalPathCompletion20261011 Space) : SkorokhodGlobalPathCompletion20261011 Space :=
  skorokhodGlobalFiniteReconstructionCompletion20261011
    (skorokhodGlobalRegularGridSelectionCompletion20261011 horizon grid)
    (fun index => path (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid index))

theorem skorokhodGlobalRegularReconstruction_profile_bound_completion20261011
    (horizon grid : ℕ) (path : SkorokhodGlobalPathCompletion20261011 Space)
    (duration tolerance : ℝ) (toleranceNonnegative : 0 ≤ tolerance)
    (mesh : (horizon+1 : ℝ) / (grid+1 : ℝ) < duration)
    (modulus : ∀ first second : ℝ≥0, first ≤ horizon+1 → second ≤ horizon+1 →
      dist first second < duration → dist (path first) (path second) ≤ tolerance)
    (index : ℕ) (before : index ≤ horizon) :
    dist (skorokhodIntegerProfileCompletion20261011 path index)
      (skorokhodIntegerProfileCompletion20261011
        (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid path) index) ≤ tolerance := by
  apply (edist_le_ofReal toleranceNonnegative).mp
  apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
  apply iSup_le
  intro time
  let physical : ℝ≥0 := (index+1 : ℝ≥0) * ⟨time.val, time.property.1⟩
  have physicalBefore : physical ≤ horizon+1 := by
    have small : physical ≤ index+1 := by
      apply NNReal.coe_le_coe.mp
      change (index+1 : ℝ) * (time : ℝ) ≤ (index+1 : ℝ)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left time.property.2 (by positivity : 0 ≤ (index+1 : ℝ))
    exact small.trans (by exact_mod_cast Nat.add_le_add_right before 1)
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  exact modulus physical
    (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid
      (skorokhodGlobalRegularGridSelectionCompletion20261011 horizon grid physical))
    physicalBefore (skorokhodGlobalRegularGridPoint_le_completion20261011 _ _ _)
    ((skorokhodGlobalRegularGridSelection_near_completion20261011 _ _ _ physicalBefore).trans mesh)

end
end IGSIII34.Diffusion

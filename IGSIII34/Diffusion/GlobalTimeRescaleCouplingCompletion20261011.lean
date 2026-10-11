import IGSIII34.Diffusion.SkorokhodGlobalFiniteGridCompletion20261011
import IGSIII34.Diffusion.PathWeakAECouplingTransferCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def skorokhodGlobalTimeScaleCompletion20261011 (scale : ℝ≥0)
    (path : SkorokhodGlobalPathCompletion20261011 Space) : SkorokhodGlobalPathCompletion20261011 Space :=
  ⟨fun time => path (scale*time)⟩

/-- A converging deterministic clock ratio changes an actual path law by
an error tending to zero in probability in the whole genuine J1 metric.
The only stochastic estimate used is the proved physical-time modulus. -/
theorem skorokhodGlobal_time_scale_coupling_probability_completion20261011
    {Samples : ℕ → Type*} [∀ index, MeasurableSpace (Samples index)]
    (laws : ∀ index, Measure (Samples index))
    (samples : ∀ index, Samples index → SkorokhodGlobalPathCompletion20261011 Space)
    (scales : ℕ → ℝ≥0) (scale : ℝ≥0) (convergence : Tendsto scales atTop (𝓝 scale))
    (modulus : ∀ horizon : ℝ≥0, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ index in atTop,
        ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
          ∀ outcome ∉ bad, ∀ first second : ℝ≥0, first ≤ horizon → second ≤ horizon →
            dist first second < duration → dist (samples index outcome first) (samples index outcome second) ≤ tolerance)
    (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∀ᶠ index in atTop, ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
      ∀ outcome ∉ bad, dist (skorokhodGlobalTimeScaleCompletion20261011 (scales index) (samples index outcome))
        (skorokhodGlobalTimeScaleCompletion20261011 scale (samples index outcome)) ≤ tolerance := by
  have tail : Tendsto (fun count : ℕ => 2*(2:ℝ)⁻¹^count) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹ < 1)).const_mul 2
  obtain ⟨count, tailSmall⟩ := (tail.eventually (gt_mem_nhds (by positivity : 0 < tolerance/2))).exists
  let spatialTolerance : ℝ := tolerance/(2*(count+1:ℝ))
  have spatialPositive : 0 < spatialTolerance := by dsimp [spatialTolerance]; positivity
  have totalSmall : count*spatialTolerance + 2*(2:ℝ)⁻¹^count ≤ tolerance := by
    have finitePart : count*spatialTolerance ≤ tolerance/2 := by
      dsimp [spatialTolerance]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2*(count+1:ℝ))).mpr
      nlinarith [show (0:ℝ) ≤ count from Nat.cast_nonneg count]
    linarith
  let horizon : ℝ≥0 := (scale+1)*(count+1)
  obtain ⟨duration, durationPositive, probabilities⟩ := modulus horizon spatialTolerance error spatialPositive errorPositive
  have scaleBound : ∀ᶠ index in atTop, scales index < scale+1 := convergence.eventually (gt_mem_nhds (by simp))
  have scaleNear : ∀ᶠ index in atTop, dist (scales index) scale < duration/(count+1:ℝ) :=
    convergence.eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [probabilities, scaleBound, scaleNear] with index probability bound near
  obtain ⟨bad, badMeasurable, badProbability, good⟩ := probability
  refine ⟨bad, badMeasurable, badProbability, ?_⟩
  intro outcome outside
  apply (skorokhodGlobal_dist_finite_profile_bound_completion20261011 _ _ count spatialTolerance ?_).trans totalSmall
  intro coordinate before
  apply (edist_le_ofReal spatialPositive.le).mp
  apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
  apply iSup_le
  intro time
  let physical : ℝ≥0 := (coordinate+1:ℝ≥0)*⟨time.val,time.property.1⟩
  have physicalBound : physical ≤ count+1 := by
    have one : (⟨time.val,time.property.1⟩ : ℝ≥0) ≤ 1 := time.property.2
    have first := mul_le_mul_of_nonneg_left one (show 0 ≤ (coordinate+1:ℝ≥0) from bot_le)
    rw [mul_one] at first
    apply first.trans
    have raw : (coordinate:ℝ≥0)+1 ≤ (count:ℝ≥0)+1 := by
      simpa only [add_comm] using add_le_add_right (show (coordinate:ℝ≥0) ≤ count from by exact_mod_cast before.le) 1
    convert raw using 1 <;> rfl
  have firstBound : scales index*physical ≤ horizon :=
    mul_le_mul bound.le physicalBound (by positivity) (by positivity)
  have secondBound : scale*physical ≤ horizon :=
    mul_le_mul (show scale ≤ scale+1 from by simp) physicalBound (by positivity) (by positivity)
  have physicalNear : dist (scales index*physical) (scale*physical) < duration := by
    have identity : dist (scales index*physical) (scale*physical) = dist (scales index) scale * (physical : ℝ) := by
      change |(scales index:ℝ)*(physical:ℝ)-(scale:ℝ)*(physical:ℝ)| = |(scales index:ℝ)-(scale:ℝ)| * (physical:ℝ)
      rw [← sub_mul, abs_mul]
      congr 1
      exact abs_of_nonneg physical.property
    rw [identity]
    have physicalReal : (physical:ℝ) ≤ (count+1:ℝ) := NNReal.coe_le_coe.mpr physicalBound
    have ratio := (lt_div_iff₀ (by positivity : 0 < (count+1:ℝ))).mp near
    exact (mul_le_mul_of_nonneg_left physicalReal dist_nonneg).trans_lt ratio
  change edist (samples index outcome (scales index*physical)) (samples index outcome (scale*physical)) ≤ ENNReal.ofReal spatialTolerance
  apply (edist_le_ofReal spatialPositive.le).mpr
  exact good outcome outside _ _ firstBound secondBound physicalNear

end
end IGSIII34.Diffusion

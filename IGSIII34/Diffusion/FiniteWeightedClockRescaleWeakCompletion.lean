import IGSIII34.Diffusion.FiniteWeightedGlobalWeakCompletion
import IGSIII34.Diffusion.ClockAccelerationTransferCompletion
import IGSIII34.Diffusion.TimeScaleSampleMeasurabilityCompletion

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal BigOperators
variable {Space Outcome : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [MeasurableSpace Outcome]

/-- Changing a deterministic positive acceleration rescales the genuine
limiting continuous process. The proof covers the original state-weighted
exponential clocks; no convergence of those weighted paths is assumed. -/
theorem finiteWeighted_varying_clock_weak_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, Nonempty (Vertices depth)]
    [∀ depth, DecidableEq (Vertices depth)] [∀ depth, MeasurableSpace (Vertices depth)]
    [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth))
    (weights : ∀ depth, Vertices depth → ℝ) (weightsPositive : ∀ depth vertex, 0 < weights depth vertex)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (weightsBounded : ∀ depth vertex, weights depth vertex ≤ bound)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop) (placement : ∀ depth, Vertices depth → Space)
    (centeredClock : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth))
        {trajectory | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧ acceleration depth * tolerance <
          |centeredWeightClockCompletion (fun index => weights depth (trajectory index)) count|}) atTop (𝓝 0))
    (ratios : ℕ → ℝ≥0) (ratiosPositive : ∀ depth, 0 < ratios depth) (ratio : ℝ≥0) (ratioPositive : 0 < ratio)
    (ratioConvergence : Tendsto ratios atTop (𝓝 ratio))
    (law : ProbabilityMeasure Outcome) (sample : Outcome → ℝ≥0 → Space)
    (continuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (finiteMarginals : ∀ count (times : Fin count → ℝ≥0),
      Tendsto (fun depth => ProbabilityMeasure.map
        (⟨finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth), inferInstance⟩ : ProbabilityMeasure (ℕ → Vertices depth))
        ((measurable_pi_lambda _ fun coordinate => (measurable_of_finite (placement depth)).comp
          (measurable_pi_apply ⌊acceleration depth * times coordinate⌋₊)).aemeasurable)) atTop
        (𝓝 (law.map ((measurable_pi_lambda _ fun coordinate => evaluations (times coordinate)).aemeasurable))))
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion (placement depth) (acceleration depth) horizon duration tolerance) ≤ error) :
    Tendsto (fun depth => finiteWeightedGlobalSkorokhodProbabilityCompletion
      (endpoint depth) (positiveDegree depth) (initial depth) (weights depth) (weightsPositive depth)
      (acceleration depth * (ratios depth : ℝ)) (mul_pos (accelerationPositive depth) (NNReal.coe_pos.mpr (ratiosPositive depth))) (placement depth)) atTop
      (𝓝 (law.map (continuousGlobalFamily_measurable_completion
        (fun outcome time => sample outcome (ratio*time))
        (fun outcome => (continuous outcome).comp (continuous_const.mul continuous_id))
        (fun time => evaluations (ratio*time))).aemeasurable)) := by
  let laws := fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)
  let samples := fun depth => discreteGlobalSkorokhodSampleCompletion (acceleration depth) (placement depth)
  have realConvergence : Tendsto (fun depth => (ratios depth : ℝ)) atTop (𝓝 (ratio:ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ratioConvergence
  let upper : ℕ := ⌈(ratio:ℝ)⌉₊ + 1
  have upperPositive : 0 < upper := by dsimp only [upper]; omega
  have upperLimit : (ratio:ℝ) < (upper:ℝ) := by
    have before := Nat.le_ceil (ratio:ℝ)
    dsimp only [upper]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have lowerPositive : 0 < (ratio:ℝ)/2 := by positivity
  have bounds : ∀ᶠ depth in atTop, (ratio:ℝ)/2 * acceleration depth ≤ acceleration depth*(ratios depth:ℝ) ∧
      acceleration depth*(ratios depth:ℝ) ≤ (upper:ℝ)*acceleration depth := by
    filter_upwards [realConvergence.eventually (lt_mem_nhds (by linarith : (ratio:ℝ)/2 < ratio)),
      realConvergence.eventually (gt_mem_nhds upperLimit)] with depth lowerBound upperBound
    have first := mul_le_mul_of_nonneg_right lowerBound.le (accelerationPositive depth).le
    have second := mul_le_mul_of_nonneg_right upperBound.le (accelerationPositive depth).le
    constructor <;> nlinarith
  have newDiverges : Tendsto (fun depth => acceleration depth*(ratios depth:ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (bounds.mono fun _ bound => bound.1) (diverge.const_mul_atTop lowerPositive)
  have physical := finiteFloor_physical_modulus_of_chain_completion Vertices laws placement
    (fun depth => measurable_of_finite _) acceleration (fun depth => (accelerationPositive depth).le) chainModulus
  have discrete := skorokhodGlobal_varying_time_scale_weak_completion laws samples
    (fun depth time => (measurable_of_finite (placement depth)).comp (measurable_pi_apply ⌊acceleration depth*time⌋₊))
    ratios ratio ratioConvergence
    (fun depth => (timeScale_discrete_sample_measurable_completion (ratios depth) (acceleration depth) (accelerationPositive depth).le (placement depth)).aemeasurable)
    (fun depth => (timeScale_discrete_sample_measurable_completion ratio (acceleration depth) (accelerationPositive depth).le (placement depth)).aemeasurable)
    (law:Measure Outcome) sample continuous evaluations finiteMarginals physical
  have newDiscrete : Tendsto (fun depth => discreteGlobalSkorokhodProbabilityCompletion
      (endpoint depth) (positiveDegree depth) (initial depth) (acceleration depth*(ratios depth:ℝ))
      (mul_pos (accelerationPositive depth) (NNReal.coe_pos.mpr (ratiosPositive depth))).le (placement depth)) atTop
      (𝓝 (law.map (continuousGlobalFamily_measurable_completion
        (fun outcome time => sample outcome (ratio*time))
        (fun outcome => (continuous outcome).comp (continuous_const.mul continuous_id))
        (fun time => evaluations (ratio*time))).aemeasurable)) := by
    convert discrete using 1
    · funext depth
      apply Subtype.ext
      change (laws depth).map (discreteGlobalSkorokhodSampleCompletion
        (acceleration depth*(ratios depth:ℝ)) (placement depth)) =
        (laws depth).map (fun trajectory => skorokhodGlobalTimeScaleCompletion (ratios depth)
          (discreteGlobalSkorokhodSampleCompletion (acceleration depth) (placement depth) trajectory))
      congr 1
      funext trajectory
      exact (timeScale_discrete_sample_identity_completion (ratios depth) (acceleration depth) (placement depth) trajectory).symm
    · congr 1
  apply finiteWeighted_global_weak_of_discrete_completion Vertices Edges endpoint positiveDegree initial weights weightsPositive
    bound boundNonnegative weightsBounded _ (fun depth => mul_pos (accelerationPositive depth) (NNReal.coe_pos.mpr (ratiosPositive depth)))
    newDiverges placement ?_ _ newDiscrete ?_
  · exact centered_clock_change_probability_completion Vertices laws weights acceleration _ (upper:ℝ) ((ratio:ℝ)/2)
      (by exact_mod_cast upperPositive) lowerPositive bounds centeredClock
  · exact chain_modulus_clock_change_completion Vertices laws placement acceleration _
      (fun depth => (accelerationPositive depth).le) upper upperPositive (bounds.mono fun _ bound => bound.2) chainModulus

end
end IGSIII34.Diffusion

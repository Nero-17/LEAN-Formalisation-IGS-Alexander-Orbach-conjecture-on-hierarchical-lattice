import IGSIII34.Diffusion.CTClockCouplingProbabilityCompletion
import IGSIII34.Diffusion.DiscreteGlobalSkorokhodSampleCompletion
import IGSIII34.Diffusion.SkorokhodGlobalFiniteGridCompletion

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal

/-- The actual product coupling is close in the genuine whole-time
integer-horizon J1 metric. Almost-sure sample agreement allows a single
measurable null-set repair of the holding-clock path. -/
theorem continuousClock_global_coupling_probability_completion
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (Vertices : ℕ → Type*) [∀ depth, Fintype (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    (laws : ∀ depth, Measure (ℕ → Vertices depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (placement : ∀ depth, Vertices depth → Space)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop)
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (laws depth).real (finiteIntervalChainBadModulusCompletion
          (placement depth) (acceleration depth) horizon duration tolerance) ≤ error)
    (samples : ∀ depth, ((ℕ → Vertices depth) × (ℕ → ℝ)) → SkorokhodGlobalPathCompletion Space)
    (agreement : ∀ depth, ∀ᵐ outcome ∂(laws depth).prod exponentialHoldingTimeLaw,
      ∀ time : ℝ≥0, samples depth outcome time =
        placement depth (holdingTimePath outcome.1 outcome.2 (acceleration depth * (time : ℝ))))
    (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∀ᶠ depth in atTop,
      ∃ bad : Set ((ℕ → Vertices depth) × (ℕ → ℝ)),
        MeasurableSet bad ∧ ((laws depth).prod exponentialHoldingTimeLaw).real bad ≤ error ∧
        ∀ outcome ∉ bad, dist (samples depth outcome)
          (discreteGlobalSkorokhodSampleCompletion (acceleration depth) (placement depth) outcome.1) ≤ tolerance := by
  have tail : Tendsto (fun count : ℕ => 2 * (2 : ℝ)⁻¹ ^ count) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 2
  obtain ⟨count, tailSmall⟩ := (tail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < tolerance / 2))).exists
  let spatialTolerance := tolerance / (2 * (count + 1 : ℝ))
  have spatialPositive : 0 < spatialTolerance := by positivity
  have totalSmall : count * spatialTolerance + 2 * (2 : ℝ)⁻¹ ^ count ≤ tolerance := by
    have finitePart : count * spatialTolerance ≤ tolerance / 2 := by
      dsimp only [spatialTolerance]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (count + 1 : ℝ))).mpr
      have nonnegative : (0 : ℝ) ≤ count := Nat.cast_nonneg count
      nlinarith
    linarith
  filter_upwards [continuousClock_uniform_coupling_probability_completion Vertices laws placement
    (fun depth => measurable_of_finite _) acceleration accelerationPositive diverge chainModulus count spatialTolerance error spatialPositive errorPositive]
    with depth coupling
  obtain ⟨bad, badMeasurable, badProbability, uniformlyClose⟩ := coupling
  let discrepancy := {outcome : ((ℕ → Vertices depth) × (ℕ → ℝ)) | ¬∀ time : ℝ≥0, samples depth outcome time =
    placement depth (holdingTimePath outcome.1 outcome.2 (acceleration depth * (time : ℝ)))}
  let discrepancyBad := toMeasurable ((laws depth).prod exponentialHoldingTimeLaw) discrepancy
  have discrepancyZero : ((laws depth).prod exponentialHoldingTimeLaw).real discrepancyBad = 0 := by
    change (((laws depth).prod exponentialHoldingTimeLaw) discrepancyBad).toReal = 0
    rw [measure_toMeasurable, (ae_iff).mp (agreement depth), ENNReal.toReal_zero]
  refine ⟨bad ∪ discrepancyBad, badMeasurable.union (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · exact (measureReal_union_le _ _).trans (by simpa only [discrepancyZero, add_zero] using badProbability)
  · intro outcome outside
    have good : outcome ∉ bad := fun belongs => outside (Or.inl belongs)
    have formula : ∀ time : ℝ≥0, samples depth outcome time =
        placement depth (holdingTimePath outcome.1 outcome.2 (acceleration depth * (time : ℝ))) := by
      by_contra failure
      exact outside (Or.inr ((subset_toMeasurable _ discrepancy) failure))
    apply (skorokhodGlobal_dist_finite_profile_bound_completion _ _ count spatialTolerance ?_).trans totalSmall
    intro index before
    apply (edist_le_ofReal spatialPositive.le).mp
    apply (skorokhodJ1EDist_le_uniform_completion _ _).trans
    apply iSup_le
    intro time
    apply (edist_le_ofReal spatialPositive.le).mpr
    let physicalTime : ℝ≥0 := (index + 1 : ℝ≥0) * ⟨time.val, time.property.1⟩
    have timeBound : (physicalTime : ℝ) ≤ count := by
      calc
        _ = (index + 1 : ℝ) * time.val := by
          simp only [physicalTime, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
          rfl
        _ ≤ (index + 1 : ℕ) := by
          rw [Nat.cast_add, Nat.cast_one]
          have bound := mul_le_mul_of_nonneg_left time.property.2 (by positivity : (0 : ℝ) ≤ index + 1)
          have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
          rw [realLE] at bound
          simpa only [mul_one] using bound
        _ ≤ count := by exact_mod_cast Nat.succ_le_of_lt before
    change dist (samples depth outcome physicalTime)
      (placement depth (outcome.1 ⌊acceleration depth * (physicalTime : ℝ)⌋₊)) ≤ spatialTolerance
    rw [formula]
    exact uniformlyClose outcome good (physicalTime : ℝ) physicalTime.property timeBound

end
end IGSIII34.Diffusion

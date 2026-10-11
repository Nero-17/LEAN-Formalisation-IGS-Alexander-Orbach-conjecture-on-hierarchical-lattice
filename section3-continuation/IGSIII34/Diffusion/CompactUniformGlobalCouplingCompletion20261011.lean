import IGSIII34.Diffusion.SkorokhodGlobalFiniteGridCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal

/-- Uniform closeness on every bounded interval gives closeness of the
entire paths in the genuine integer-horizon Skorokhod metric. The
original sample spaces and laws may vary with the index. -/
theorem compact_uniform_global_coupling_probability_completion20261011
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    (Outcomes : ℕ → Type*) [∀ index, MeasurableSpace (Outcomes index)]
    (laws : ∀ index, Measure (Outcomes index))
    (samples approximations : ∀ index, Outcomes index → SkorokhodGlobalPathCompletion20261011 Space)
    (compactCoupling : ∀ horizon : ℕ, ∀ tolerance error : ℝ,
      0 < tolerance → 0 < error → ∀ᶠ index in atTop,
        ∃ bad : Set (Outcomes index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
          ∀ outcome ∉ bad, ∀ time : ℝ≥0, (time : ℝ) ≤ horizon →
            dist (samples index outcome time) (approximations index outcome time) ≤ tolerance)
    (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∀ᶠ index in atTop,
      ∃ bad : Set (Outcomes index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
        ∀ outcome ∉ bad,
          dist (samples index outcome) (approximations index outcome) ≤ tolerance := by
  have tail : Tendsto (fun count : ℕ => 2 * (2 : ℝ)⁻¹ ^ count) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 2
  obtain ⟨count, tailSmall⟩ :=
    (tail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < tolerance / 2))).exists
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
  filter_upwards [compactCoupling count spatialTolerance error spatialPositive errorPositive]
    with index coupling
  obtain ⟨bad, measurableBad, probabilityBad, uniformlyClose⟩ := coupling
  refine ⟨bad, measurableBad, probabilityBad, ?_⟩
  intro outcome outside
  apply (skorokhodGlobal_dist_finite_profile_bound_completion20261011 _ _ count spatialTolerance ?_).trans totalSmall
  intro profile before
  apply (edist_le_ofReal spatialPositive.le).mp
  apply (skorokhodJ1EDist_le_uniform_completion20261011 _ _).trans
  apply iSup_le
  intro time
  apply (edist_le_ofReal spatialPositive.le).mpr
  let physicalTime : ℝ≥0 := (profile + 1 : ℝ≥0) * ⟨time.val, time.property.1⟩
  have timeBound : (physicalTime : ℝ) ≤ count := by
    calc
      _ = (profile + 1 : ℝ) * time.val := by
        simp only [physicalTime, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
        rfl
      _ ≤ (profile + 1 : ℕ) := by
        rw [Nat.cast_add, Nat.cast_one]
        have bound := mul_le_mul_of_nonneg_left time.property.2 (by positivity : (0 : ℝ) ≤ profile + 1)
        have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
        rw [realLE] at bound
        simpa only [mul_one] using bound
      _ ≤ count := by exact_mod_cast Nat.succ_le_of_lt before
  change dist (samples index outcome physicalTime) (approximations index outcome physicalTime) ≤ spatialTolerance
  exact uniformlyClose outcome outside physicalTime timeBound

end
end IGSIII34.Diffusion

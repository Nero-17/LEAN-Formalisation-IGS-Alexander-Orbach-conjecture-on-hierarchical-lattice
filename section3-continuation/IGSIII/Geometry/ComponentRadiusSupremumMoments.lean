import IGSIII.Probability.DescendantLpEnvelope
import IGSIII.Geometry.UniformRadiusAmplitude
import IGSIII.Geometry.CriticalChemicalLengths
import IGSIII.Geometry.RetainedComponentDiameter

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The actual radius, normalized in the local root units, uniformly over all
remaining depths. Both noncrossing components are included by their radii. -/
def markedComponentRadiusSupremum (rule : Rule) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened : Bool)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  ⨆ depth, (markedTerminalComponentRadius rule marks depth address opened : ℝ) / growth ^ (depth + 1)

lemma markedTerminalComponentRadius_measurable (rule : Rule) (depth : ℕ)
    (address : List (Fin rule.edges)) (opened : Bool) :
    Measurable (fun marks => markedTerminalComponentRadius rule marks depth address opened) :=
  (measurable_of_finite (fun configuration => terminalComponentRadius (rule.generation depth).network configuration)).comp
    (markedGenerationConfiguration_measurable rule depth address opened)

lemma markedComponentRadiusSupremum_measurable (rule : Rule) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened : Bool) :
    Measurable (markedComponentRadiusSupremum rule growth address opened) :=
  Measurable.iSup (fun depth => ((measurable_of_countable (fun value : ℕ => (value : ℝ))).comp (markedTerminalComponentRadius_measurable rule depth address opened)).div_const _)

/-- All positive moments of the supremum follow from a high moment of the
terminal envelopes and the actual component-radius recursion. -/
theorem markedComponentRadiusSupremum_memLp_of_terminal_envelopes
    (rule : Rule)
    (probability : Measure (((List (Fin rule.edges) × Bool) → Configuration rule.edges)))
    [IsProbabilityMeasure probability] (growth : ℝ) (growthGreaterThanOne : 1 < growth)
    (functions : List (Fin rule.edges) → Bool →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (measurable : ∀ address opened, Measurable (functions address opened))
    (moments : ∀ power : ℕ, 0 < power → ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧
      ∀ address opened, eLpNorm (functions address opened) power probability ≤ bound)
    (terminalBound : ∀ᵐ marks ∂probability, ∀ address opened depth,
      (markedTerminalDistance rule marks depth address opened : ℝ) / growth ^ (depth + 1) ≤ functions address opened marks)
    (order : ℝ≥0∞) (orderFinite : order ≠ ∞) :
    (∀ address opened, MemLp (markedComponentRadiusSupremum rule growth address opened) order probability) ∧
    ∀ᵐ marks ∂probability, ∀ address opened depth,
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / growth ^ (depth + 1) ≤
        markedComponentRadiusSupremum rule growth address opened marks := by
  let eta : ℝ := (1 + growth⁻¹) / 2
  have growthPositive : 0 < growth := zero_lt_one.trans growthGreaterThanOne
  have etaPositive : 0 < eta := by dsimp [eta]; positivity
  have etaBelowOne : eta < 1 := by
    have : growth⁻¹ < 1 := inv_lt_one_of_one_lt₀ growthGreaterThanOne
    dsimp [eta]
    linarith
  have productGreaterThanOne : 1 < growth * eta := by
    dsimp [eta]
    field_simp
    nlinarith
  have productPositive : 0 < growth * eta := mul_pos growthPositive etaPositive
  obtain ⟨minimumOrder, minimumOrderBound⟩ := ENNReal.exists_nat_gt orderFinite
  have largePower := (tendsto_pow_atTop_atTop_of_one_lt productGreaterThanOne).eventually
    (eventually_gt_atTop (rule.edges : ℝ))
  obtain ⟨power, ⟨powerPositive, orderBound⟩, momentGrowth⟩ :=
    (((eventually_gt_atTop (0 : ℕ)).and (eventually_ge_atTop minimumOrder)).and largePower).exists
  have orderLePower : order ≤ (power : ℝ≥0∞) :=
    minimumOrderBound.le.trans (by exact_mod_cast orderBound)
  have decay : (rule.edges : ℝ≥0∞) * (ENNReal.ofReal (growth * eta))⁻¹ ^ power < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos productPositive,
      ← ENNReal.ofReal_pow (inv_nonneg.mpr productPositive.le),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg rule.edges)]
    apply ENNReal.ofReal_lt_one.mpr
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_lt_one (pow_pos productPositive power)).mpr momentGrowth
  obtain ⟨bound, boundFinite, momentBounds⟩ := moments power powerPositive
  obtain ⟨envelope, envelopeMeasurable, envelopeMemLp, envelopeNonnegative, envelopeBounds⟩ :=
    IGSIII.Probability.exists_memLp_descendant_envelope probability rule.edges power powerPositive functions
      measurable bound boundFinite momentBounds (growth * eta) productPositive decay
  let amplitude : (((List (Fin rule.edges) × Bool) → Configuration rule.edges)) → ℝ := fun marks => 1 + envelope marks
  have amplitudeMeasurable : Measurable amplitude := measurable_const.add envelopeMeasurable
  have amplitudeMemLp : MemLp amplitude order probability :=
    ((memLp_const (1 : ℝ)).add envelopeMemLp).mono_exponent orderLePower
  have amplitudeLarge (marks) : 1 ≤ amplitude marks := by dsimp [amplitude]; linarith [envelopeNonnegative marks]
  let coefficient : ℝ := (rule.edges + 1 : ℝ) / (1 - eta)
  have coefficientLarge : (rule.edges : ℝ) ≤ coefficient := by
    dsimp [coefficient]
    apply (le_div_iff₀ (sub_pos.mpr etaBelowOne)).mpr
    nlinarith [show (0 : ℝ) ≤ (rule.edges : ℝ) from Nat.cast_nonneg _]
  have coefficientNonnegative : 0 ≤ coefficient := (Nat.cast_nonneg rule.edges).trans coefficientLarge
  have coefficientContracts : eta * (coefficient + rule.edges) ≤ coefficient := by
    have formula : coefficient * (1 - eta) = rule.edges + 1 :=
      div_mul_cancel₀ _ (sub_pos.mpr etaBelowOne).ne'
    have edgesBound : eta * rule.edges ≤ (rule.edges : ℝ) :=
      mul_le_of_le_one_left (Nat.cast_nonneg _) etaBelowOne.le
    nlinarith
  have radiusBounds : ∀ᵐ marks ∂probability, ∀ depth address opened,
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / growth ^ (depth + 1) ≤
        (coefficient * amplitude marks) * (growth * eta) ^ address.length := by
    filter_upwards [terminalBound, envelopeBounds] with marks terminals envelopes
    have coefficientAmplitudeLarge : (rule.edges : ℝ) ≤ coefficient * amplitude marks :=
      coefficientLarge.trans (le_mul_of_one_le_right coefficientNonnegative (amplitudeLarge marks))
    have amplifiedContract : eta * (coefficient * amplitude marks + rule.edges * amplitude marks) ≤
        coefficient * amplitude marks := by
      nlinarith [mul_le_mul_of_nonneg_right coefficientContracts (by linarith [amplitudeLarge marks])]
    have radius := marked_radius_uniform_bound_of_amplified_terminal_envelope rule marks growth eta
      (coefficient * amplitude marks) (amplitude marks) 0 (by linarith [amplitudeLarge marks])
      growthGreaterThanOne etaPositive productGreaterThanOne.le coefficientAmplitudeLarge amplifiedContract
      (fun address opened depth _ => by
        have normalized := (terminals address opened depth).trans
          ((show functions address opened marks ≤ ‖functions address opened marks‖ by simpa only [Real.norm_eq_abs] using le_abs_self _).trans (envelopes address opened))
        have amplitudeBound : envelope marks * (growth * eta) ^ address.length ≤
            amplitude marks * (growth * eta) ^ address.length := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg productPositive.le _)
          dsimp [amplitude]
          linarith
        have := (div_le_iff₀ (pow_pos growthPositive (depth + 1))).mp (normalized.trans amplitudeBound)
        simpa only [mul_comm, mul_left_comm, mul_assoc] using this)
    intro depth address opened
    exact (div_le_iff₀ (pow_pos growthPositive (depth + 1))).mpr (by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using radius depth address opened (Nat.zero_le _))
  have supremumProperties (address : List (Fin rule.edges)) (opened : Bool) :=
    IGSIII.Probability.supremum_memLp_of_lp_dominator probability order
      (fun depth marks => (markedTerminalComponentRadius rule marks depth address opened : ℝ) / growth ^ (depth + 1))
      (fun depth => ((measurable_of_countable (fun value : ℕ => (value : ℝ))).comp (markedTerminalComponentRadius_measurable rule depth address opened)).div_const _)
      (Eventually.of_forall (fun marks depth => div_nonneg (Nat.cast_nonneg _) (pow_nonneg growthPositive.le _)))
      ((amplitudeMemLp.const_mul coefficient).mul_const ((growth * eta) ^ address.length)).toLp
      (by
        filter_upwards [radiusBounds, MemLp.coeFn_toLp
          ((amplitudeMemLp.const_mul coefficient).mul_const ((growth * eta) ^ address.length))] with marks bounds identity
        rw [identity]
        exact fun depth => bounds depth address opened)
  refine ⟨fun address opened => (supremumProperties address opened).1, ?_⟩
  exact ae_all_iff.mpr (fun address => ae_all_iff.mpr (fun opened => (supremumProperties address opened).2))

end
end IGSIII.Geometry


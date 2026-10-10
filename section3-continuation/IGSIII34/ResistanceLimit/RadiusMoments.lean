import IGSIII34.ResistanceLimit.RadiusEnvelope
import IGSIII.Probability.DescendantLpEnvelope
import IGSIII34.ResistanceLimit.TerminalEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The actual unit-resistance radius of both terminal components, uniformly
over all remaining generations in the local normalization. -/
def markedElectricalRadiusSupremum (rule : Rule) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened : Bool)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  ⨆ depth, markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1)

lemma markedElectricalRadius_measurable (rule : Rule) (depth : ℕ)
    (address : List (Fin rule.edges)) (opened : Bool) :
    Measurable (fun marks => markedElectricalRadius rule marks depth address opened) :=
  (measurable_of_finite (fun configuration => terminalResistanceRadius
    (network (rule.generation depth).network configuration) (fun _ => 1))).comp
      (markedGenerationConfiguration_measurable rule depth address opened)

lemma markedElectricalRadiusSupremum_measurable (rule : Rule) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened : Bool) :
    Measurable (markedElectricalRadiusSupremum rule growth address opened) :=
  Measurable.iSup (fun depth => (markedElectricalRadius_measurable rule depth address opened).div_const _)

/-- The full electrical radius recursion upgrades uniform terminal moments
to moments of the supremum over all finite depths. No component is pruned. -/
theorem markedElectricalRadiusSupremum_memLp_of_terminal_envelopes
    (rule : Rule)
    (probability : Measure (((List (Fin rule.edges) × Bool) → Configuration rule.edges)))
    [IsProbabilityMeasure probability] (growth : ℝ) (growthGreaterThanOne : 1 < growth)
    (terminalEnvelopes : ∀ power : ℕ, 0 < power →
      ∃ functions : List (Fin rule.edges) → Bool →
        (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧
        (∀ address opened, Measurable (functions address opened)) ∧
        (∀ address opened, eLpNorm (functions address opened) power probability ≤ bound) ∧
        ∀ᵐ marks ∂probability, ∀ address opened depth,
          unitConfigurationResistance (rule.generation depth).network
            (markedGenerationConfiguration rule marks depth address opened) / growth ^ (depth + 1) ≤
              functions address opened marks)
    (order : ℝ≥0∞) (orderFinite : order ≠ ∞) :
    (∀ address opened, MemLp (markedElectricalRadiusSupremum rule growth address opened) order probability) ∧
    ∀ᵐ marks ∂probability, ∀ address opened depth,
      markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1) ≤
        markedElectricalRadiusSupremum rule growth address opened marks := by
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
  obtain ⟨functions, bound, boundFinite, measurable, momentBounds, terminalBound⟩ :=
    terminalEnvelopes power powerPositive
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
      markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1) ≤
        (coefficient * amplitude marks) * (growth * eta) ^ address.length := by
    filter_upwards [terminalBound, envelopeBounds] with marks terminals envelopes
    have coefficientAmplitudeLarge : (rule.edges : ℝ) ≤ coefficient * amplitude marks :=
      coefficientLarge.trans (le_mul_of_one_le_right coefficientNonnegative (amplitudeLarge marks))
    have amplifiedContract : eta * (coefficient * amplitude marks + rule.edges * amplitude marks) ≤
        coefficient * amplitude marks := by
      nlinarith [mul_le_mul_of_nonneg_right coefficientContracts (by linarith [amplitudeLarge marks])]
    have radius := marked_electrical_radius_uniform_bound rule marks growth eta
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
      (fun depth marks => markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1))
      (fun depth => (markedElectricalRadius_measurable rule depth address opened).div_const _)
      (Eventually.of_forall (fun marks depth => div_nonneg (terminalResistanceRadius_nonnegative _ _) (pow_nonneg growthPositive.le _)))
      ((amplitudeMemLp.const_mul coefficient).mul_const ((growth * eta) ^ address.length)).toLp
      (by
        filter_upwards [radiusBounds, MemLp.coeFn_toLp
          ((amplitudeMemLp.const_mul coefficient).mul_const ((growth * eta) ^ address.length))] with marks bounds identity
        rw [identity]
        exact fun depth => bounds depth address opened)
  refine ⟨fun address opened => (supremumProperties address opened).1, ?_⟩
  exact ae_all_iff.mpr (fun address => ae_all_iff.mpr (fun opened => (supremumProperties address opened).2))

theorem actual_markedElectricalRadiusSupremum_memLp_fixed_cluster
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (order : ℝ≥0∞) (orderFinite : order ≠ ∞) :
    (∀ address opened, MemLp (markedElectricalRadiusSupremum rule growth address opened) order
      (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address opened depth,
        markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1) ≤
          markedElectricalRadiusSupremum rule growth address opened marks := by
  apply markedElectricalRadiusSupremum_memLp_of_terminal_envelopes rule _ growth growthGreaterThanOne _ order orderFinite
  exact actual_terminal_resistance_envelopes_fixed_cluster rule classical p positive belowOne fixedPoint
    constant growth constantPositive (zero_lt_one.trans growthGreaterThanOne) growthBounds
    endpoint endpointFixed membership

end
end IGSIII34.ResistanceLimit

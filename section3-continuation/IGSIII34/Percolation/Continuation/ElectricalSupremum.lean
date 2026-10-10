import IGSIII34.Percolation.Continuation.ElectricalLpAllOrder
import IGSIII34.Percolation.Continuation.ElectricalReciprocal
import IGSIII.Probability.CountableLpEnvelope
import Mathlib.MeasureTheory.Integral.MeanInequalities
import IGSIII34.Probability.ReciprocalMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

theorem lintegral_enorm_pow_le_L2_mul_higher
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value : Sample → ℝ) (measurable : Measurable value) (power : ℕ) (powerAtLeastTwo : 2 ≤ power) :
    (∫⁻ sample, ‖value sample‖ₑ^power ∂measure) ≤
      eLpNorm value 2 measure *
        (eLpNorm value (ENNReal.ofReal (2*((power:ℝ)-1))) measure)^((power:ℝ)-1) := by
  have powerPositive : 0 < (power:ℝ)-1 := by
    have : (2:ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have highPositive : 0 < 2*((power:ℝ)-1) := mul_pos (by norm_num) powerPositive
  have holder := ENNReal.lintegral_mul_le_Lp_mul_Lq measure Real.HolderConjugate.two_two
    measurable.enorm.aemeasurable (measurable.enorm.pow_const ((power:ℝ)-1)).aemeasurable
  have productIdentity (sample : Sample) : ‖value sample‖ₑ * ‖value sample‖ₑ^((power:ℝ)-1) = ‖value sample‖ₑ^power := by
    nth_rw 1 [← ENNReal.rpow_one ‖value sample‖ₑ]
    rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one powerPositive.le]
    simp only [add_sub_cancel, ENNReal.rpow_natCast]
  simp only [Pi.mul_apply, productIdentity, ← ENNReal.rpow_mul, mul_comm ((power:ℝ)-1) 2] at holder
  change (∫⁻ sample, ‖value sample‖ₑ^power ∂measure) ≤
    (∫⁻ sample, ‖value sample‖ₑ^(2:ℝ) ∂measure)^(1/(2:ℝ))*
    (∫⁻ sample, ‖value sample‖ₑ^(2*((power:ℝ)-1)) ∂measure)^(1/(2:ℝ)) at holder
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠∞)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr highPositive).ne' ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal highPositive.le,
    ← ENNReal.rpow_mul]
  have exponentIdentity : 1/(2*((power:ℝ)-1))*((power:ℝ)-1)=1/(2:ℝ) := by field_simp
  simpa only [exponentIdentity] using holder

theorem conditionalLp2_enorm_bound
    {Sample : Type*} [ambient : MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (subspace : MeasurableSpace Sample) (subspaceLe : subspace ≤ ambient)
    (value : Lp ℝ 2 measure) (order : ℝ≥0∞) (orderAtLeastOne : 1 ≤ order) :
    eLpNorm (fun sample => value sample-conditionalLp2 (ambient := ambient) measure subspace subspaceLe value sample) order measure ≤
      2*eLpNorm value order measure := by
  letI : MeasurableSpace Sample := ambient
  have equality := conditionalLp2_ae_eq_condExp measure subspace subspaceLe value
  have projectionNorm : eLpNorm (conditionalLp2 measure subspace subspaceLe value) order measure ≤ eLpNorm value order measure := by
    rw [eLpNorm_congr_ae equality]
    exact eLpNorm_condExp_le_eLpNorm _ orderAtLeastOne
  apply (eLpNorm_sub_le (Lp.aestronglyMeasurable value)
    (Lp.aestronglyMeasurable (conditionalLp2 measure subspace subspaceLe value)) orderAtLeastOne).trans
  calc
    _ ≤ eLpNorm value order measure+eLpNorm value order measure := add_le_add le_rfl projectionNorm
    _ = _ := by rw [two_mul]

theorem conditional_mean_envelope_of_geometric_L2_residual
    {Sample : Type*} [ambient : MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (information : ℕ → MeasurableSpace Sample) (informationLe : ∀ depth, information depth ≤ ambient)
    (value : Lp ℝ 2 measure) (bound rate : ℝ) (boundNonnegative : 0 ≤ bound)
    (rateNonnegative : 0 ≤ rate) (rateBelowOne : rate < 1)
    (residualBound : ∀ depth, ‖value-conditionalLp2 (ambient := ambient) measure (information depth) (informationLe depth) value‖ ≤ bound*rate^depth)
    (power : ℕ) (powerAtLeastTwo : 2 ≤ power)
    (higherMemLp : MemLp value (ENNReal.ofReal (2*((power:ℝ)-1))) measure) :
    ∃ envelope : Sample → ℝ, Measurable envelope ∧ MemLp envelope power measure ∧
      (∀ sample, 0 ≤ envelope sample) ∧
      ∀ᵐ sample ∂measure, ∀ depth, ‖measure[⇑value | information depth] sample‖ ≤ envelope sample := by
  letI : MeasurableSpace Sample := ambient
  let errors (depth : ℕ) (sample : Sample) := value sample-
    conditionalLp2 measure (information depth) (informationLe depth) value sample
  have errorsMeasurable (depth : ℕ) : Measurable (errors depth) :=
    (Lp.stronglyMeasurable value).measurable.sub (Lp.stronglyMeasurable _).measurable
  have powerPositive : 0 < (power:ℝ)-1 := by
    have : (2:ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have highAtLeastOne : (1:ℝ≥0∞) ≤ ENNReal.ofReal (2*((power:ℝ)-1)) := by
    rw [ENNReal.one_le_ofReal]
    have : (2:ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have errorsL2 (depth : ℕ) : eLpNorm (errors depth) 2 measure ≤ ENNReal.ofReal (bound*rate^depth) := by
    have equality := eLpNorm_congr_ae (p := 2) (Lp.coeFn_sub value (conditionalLp2 measure (information depth) (informationLe depth) value))
    change eLpNorm (value-conditionalLp2 measure (information depth) (informationLe depth) value) 2 measure =
      eLpNorm (errors depth) 2 measure at equality
    rw [← equality, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (residualBound depth)
  have summablePowers : (∑' depth, ∫⁻ sample, ‖errors depth sample‖ₑ^power ∂measure) ≠ ∞ := by
    have estimates (depth : ℕ) : (∫⁻ sample, ‖errors depth sample‖ₑ^power ∂measure) ≤
        ENNReal.ofReal bound*(ENNReal.ofReal rate)^depth*
          (2*eLpNorm value (ENNReal.ofReal (2*((power:ℝ)-1))) measure)^((power:ℝ)-1) := by
      apply (lintegral_enorm_pow_le_L2_mul_higher measure (errors depth) (errorsMeasurable depth) power powerAtLeastTwo).trans
      calc
        _ ≤ ENNReal.ofReal (bound*rate^depth)*
            (2*eLpNorm value (ENNReal.ofReal (2*((power:ℝ)-1))) measure)^((power:ℝ)-1) := by
          exact mul_le_mul' (errorsL2 depth)
            (ENNReal.rpow_le_rpow (conditionalLp2_enorm_bound measure (information depth) (informationLe depth) value _ highAtLeastOne) powerPositive.le)
        _ = _ := by rw [ENNReal.ofReal_mul boundNonnegative, ENNReal.ofReal_pow rateNonnegative]
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum estimates)
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((tsum_geometric_lt_top.mpr (by simpa only [ENNReal.ofReal_lt_one] using rateBelowOne)).ne)
    · exact ENNReal.rpow_ne_top_of_nonneg powerPositive.le (ENNReal.mul_ne_top (by norm_num) higherMemLp.eLpNorm_ne_top)
  obtain ⟨errorEnvelope, errorMeasurable, errorMemLp, errorNonnegative, errorBounds⟩ :=
    exists_memLp_countable_envelope measure power (by omega) errors errorsMeasurable summablePowers
  have powerBound : (power:ℝ≥0∞) ≤ ENNReal.ofReal (2*((power:ℝ)-1)) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have : (2:ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have valueMemLp : MemLp value power measure := higherMemLp.mono_exponent powerBound
  refine ⟨fun sample => ‖value sample‖+errorEnvelope sample,
    (Lp.stronglyMeasurable value).measurable.norm.add errorMeasurable,
    valueMemLp.norm.add errorMemLp, fun sample => add_nonneg (norm_nonneg _) (errorNonnegative sample), ?_⟩
  have conditionalEqualities := ae_all_iff.mpr (fun depth =>
    conditionalLp2_ae_eq_condExp measure (information depth) (informationLe depth) value)
  filter_upwards [errorBounds, conditionalEqualities] with sample errorBounds equalities
  intro depth
  rw [← equalities depth]
  calc
    _ ≤ ‖value sample‖+‖errors depth sample‖ := by
      have inequality := norm_sub_le (value sample) (errors depth sample)
      simpa only [errors, sub_sub_cancel] using inequality
    _ ≤ _ := add_le_add le_rfl (errorBounds depth)

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (constantPositive : 0 < constant) (growthPositive : 0 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint
local notation "W" => electricalOrbitLp rule p positive belowOne fixedPoint growth
local notation "T" => normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth

include classical constantPositive growthPositive growthBounds in
theorem electricalOrbit_exists_memLp_uniform_envelope_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (power : ℕ) (powerAtLeastTwo : 2 ≤ power) :
    ∃ envelope : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ,
      Measurable envelope ∧ MemLp envelope power μ ∧ (∀ marks, 0 ≤ envelope marks) ∧
      ∀ᵐ marks ∂μ, ∀ depth, W depth marks ≤ envelope marks := by
  have endpointPositive := electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive
    (fun depth => (growthBounds depth).1) endpoint membership
  have moments := electricalOmega_integrable_real_moment rule classical p positive belowOne fixedPoint constant growth
    constantPositive growthPositive growthBounds endpoint membership
  obtain ⟨bound, rate, boundNonnegative, rateNonnegative, rateBelowOne, estimates⟩ :=
    exists_electricalOrbit_geometric_prefix_residual rule classical p positive belowOne fixedPoint constant growth
      constantPositive growthPositive growthBounds
  have convergence := electricalOrbitLp_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
    growthPositive growthBounds endpoint endpointFixed membership
  have residualBound := electrical_limit_geometric_prefix_residual rule p positive belowOne fixedPoint growth bound rate
    estimates endpoint convergence
  have highPositive : 0 < 2*((power:ℝ)-1) := by
    have : (2:ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have normMoment : Integrable (fun marks => ‖endpoint marks‖^(2*((power:ℝ)-1))) μ := by
    apply (moments (2*((power:ℝ)-1))).congr
    filter_upwards [endpointPositive] with marks positive
    rw [Real.norm_eq_abs, abs_of_pos positive]
  have higherMemLp : MemLp endpoint (ENNReal.ofReal (2*((power:ℝ)-1))) μ := by
    apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable endpoint)
      (ENNReal.ofReal_pos.mpr highPositive).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal highPositive.le] using normMoment
  obtain ⟨meanEnvelope, meanMeasurable, meanMemLp, meanNonnegative, meanBounds⟩ :=
    conditional_mean_envelope_of_geometric_L2_residual μ
      (fun depth => coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
      (fun depth => (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)).le (depth+1))
      endpoint bound rate boundNonnegative rateNonnegative rateBelowOne residualBound power powerAtLeastTwo higherMemLp
  have inverseIntegrable : Integrable (fun marks => (endpoint marks)⁻¹) μ := by
    simpa only [Real.rpow_neg_one] using moments (-1)
  let inverseMean := ∫ marks, (endpoint marks)⁻¹ ∂μ
  have inverseMeanPositive : 0 < inverseMean := by
    have product := integral_mul_reciprocal_integral_ge_one μ endpoint (Lp.stronglyMeasurable endpoint).measurable
      endpointPositive ((Lp.memLp endpoint).integrable (by norm_num)) inverseIntegrable
    have nonnegative : 0 ≤ inverseMean := integral_nonneg_of_ae (endpointPositive.mono (fun marks positive => (inv_pos.mpr positive).le))
    by_contra failure
    have zero : inverseMean = 0 := le_antisymm (le_of_not_gt failure) nonnegative
    change 1 ≤ (∫ marks, endpoint marks ∂μ)*inverseMean at product
    rw [zero, mul_zero] at product
    norm_num at product
  have upperBounds (depth : ℕ) : ∀ᵐ marks ∂μ, W (depth+1) marks ≤
      inverseMean*μ[⇑endpoint | coordinatePrefixFiltration
        (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
    have lower := normalized_electrical_boundary_conditional_mean_lower rule p positive belowOne fixedPoint growth growthPositive.le
      endpoint endpointPositive inverseIntegrable inverseMean inverseMeanPositive rfl depth
    rw [Function.iterate_fixed endpointFixed (depth+1)] at lower
    filter_upwards [lower, electricalOrbitLp_coe_ae_unit_generation rule p positive belowOne fixedPoint growth growthPositive.le depth]
      with marks inequality equality
    rw [← equality] at inequality
    exact ((div_le_iff₀ inverseMeanPositive).mp inequality).trans_eq (mul_comm _ _)
  refine ⟨fun marks => 1+inverseMean*meanEnvelope marks,
    measurable_const.add (measurable_const.mul meanMeasurable),
    (memLp_const (1:ℝ)).add (meanMemLp.const_mul inverseMean),
    fun marks => add_nonneg zero_le_one (mul_nonneg inverseMeanPositive.le (meanNonnegative marks)), ?_⟩
  filter_upwards [meanBounds, ae_all_iff.mpr upperBounds,
    electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le 0] with marks bounds upper zero
  intro depth
  cases depth with
  | zero =>
      simp only [pow_zero, electricalIteration, one_mul] at zero
      rw [zero]
      exact le_add_of_nonneg_right (mul_nonneg inverseMeanPositive.le (meanNonnegative marks))
  | succ depth =>
      calc
        _ ≤ inverseMean*μ[⇑endpoint | coordinatePrefixFiltration
            (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := upper depth
        _ ≤ inverseMean*meanEnvelope marks := mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using bounds depth)) inverseMeanPositive.le
        _ ≤ _ := le_add_of_nonneg_left zero_le_one

include classical constantPositive growthPositive growthBounds in
theorem electricalIteration_supremum_real_moment_finite_fixed_cluster
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (address : List (Fin rule.edges)) (exponent : ℝ) (exponentPositive : 0 < exponent) :
    (∫⁻ marks, (⨆ depth : ℕ, ENNReal.ofReal (growth⁻¹^depth*electricalIteration rule marks depth address))^exponent ∂μ) ≠ ∞ := by
  obtain ⟨power, powerBound⟩ := exists_nat_gt (max exponent 2)
  have powerAtLeastTwo : 2 ≤ power := by
    have comparison : (2:ℝ) < power := (le_max_right exponent 2).trans_lt powerBound
    exact_mod_cast comparison.le
  obtain ⟨envelope, envelopeMeasurable, envelopeMemLp, envelopeNonnegative, envelopeBounds⟩ :=
    electricalOrbit_exists_memLp_uniform_envelope_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership power powerAtLeastTwo
  have orderBound : ENNReal.ofReal exponent ≤ (power:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal ((le_max_left exponent 2).trans_lt powerBound).le
  have rootBounds : ∀ᵐ marks ∂μ, ∀ depth, growth⁻¹^depth*electricalIteration rule marks depth [] ≤ envelope marks := by
    filter_upwards [envelopeBounds,
      ae_all_iff.mpr (electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le)]
      with marks bounds equalities
    intro depth
    rw [← equalities depth]
    exact bounds depth
  have preserving := innovationTreeShift_preserving rule p positive belowOne fixedPoint address
  have shiftedBounds := preserving.quasiMeasurePreserving.ae rootBounds
  simp only [electricalIteration_shift, List.append_nil] at shiftedBounds
  have shiftedMemLp := (envelopeMemLp.mono_exponent orderBound).comp_measurePreserving preserving
  have finite := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (ENNReal.ofReal_pos.mpr exponentPositive).ne'
    ENNReal.ofReal_ne_top shiftedMemLp.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal exponentPositive.le] at finite
  apply ne_top_of_le_ne_top finite.ne
  apply lintegral_mono_ae
  filter_upwards [shiftedBounds] with marks bounds
  apply ENNReal.rpow_le_rpow _ exponentPositive.le
  apply iSup_le
  intro depth
  rw [← ofReal_norm, Real.norm_eq_abs, Function.comp_def, abs_of_nonneg (envelopeNonnegative _)]
  exact ENNReal.ofReal_le_ofReal (bounds depth)

include classical in
theorem exists_actual_electrical_supremum_real_moments
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ growth : ℝ, deriv rule.network.reliability p ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
      ∀ address : List (Fin rule.edges), ∀ exponent : ℝ, 0 < exponent →
        (∫⁻ marks, (⨆ depth : ℕ, ENNReal.ofReal (growth⁻¹^depth*electricalIteration rule marks depth address))^exponent ∂μ) ≠ ∞ := by
  obtain ⟨constant, growth, constantPositive, _, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, _, _, amplitude, amplitudeLower, membership, _, _⟩ :=
    exists_actual_electrical_fixed_ray_endpoint rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthPositive := (zero_lt_one.trans
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale)).trans_le growthLower
  have endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth (amplitude • fixed) = amplitude • fixed := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 growth amplitude
      (zero_le_one.trans amplitudeLower), fixedIdentity]
  exact ⟨growth, growthLower, growthUpper,
    electricalIteration_supremum_real_moment_finite_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds (amplitude • fixed) endpointFixed membership⟩

end
end IGSIII34.Percolation

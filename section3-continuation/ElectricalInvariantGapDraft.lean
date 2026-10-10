import IGSIII34.Percolation.ElectricalTransferBounds
import IGSIII34.Probability.UniformInverse
import IGSIII.Probability.CompactEnvelopeGap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal NNReal

theorem exists_uniform_invariant_electrical_gap_thinning (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (family : Set (Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)))
    (compact : IsCompact family) (familyNonnegative : ∀ value ∈ family, 0 ≤ value)
    (mapsTo : Set.MapsTo (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth) family family)
    (onto : Set.SurjOn (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth) family family)
    (upper : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (upperFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth upper = upper)
    (upperBound : ∀ value ∈ family, value ≤ upper) (absent : upper ∉ family) :
    ∃ cutoff start : ℝ, 0 < cutoff ∧ 0 ≤ start ∧ start < 1 ∧
      ∀ value ∈ family, ∀ depth : ℕ,
        (independentInnovationLaw rule p positive belowOne fixedPoint).real
          {marks | (upper - value) marks ≤ cutoff / ((rule.edges : ℝ)*growth)^depth} ≤
          (thinningMap rule.network p)^[depth] start := by
  obtain ⟨gap, gapPositive, meanLower⟩ := compact_order_gap_has_positive_mean family compact upper upperBound absent
  have secondBound (value : {value // value ∈ family}) :
      (∫ marks, (upper - value.val) marks^2 ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
      max 1 (∫ marks, upper marks^2 ∂independentInnovationLaw rule p positive belowOne fixedPoint) :=
    (IGSIII.Chemical.SmallBall.lp2_nonnegative_gap_second_moment_le _ upper value.val
      (familyNonnegative value.val value.property) (upperBound value.val value.property)).trans (le_max_right _ _)
  obtain ⟨start, startNonnegative, startBelowOne, initial⟩ :=
    IGSIII.Chemical.SmallBall.exists_uniform_smallBall_start_of_positive_mean
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (fun value : {value // value ∈ family} => ⇑(upper - value.val))
      (fun value => (Lp.stronglyMeasurable (upper - value.val)).measurable)
      (fun value => (Lp.memLp (upper - value.val)).integrable (by norm_num))
      (fun value => (Lp.memLp (upper - value.val)).integrable_sq)
      gapPositive (zero_le_one.trans (le_max_left _ _))
      (fun value => meanLower value.val value.property) secondBound
  let successor : {value // value ∈ family} → {value // value ∈ family} := fun value =>
    ⟨normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value.val, mapsTo value.property⟩
  have successorOnto : Function.Surjective successor := by
    intro value
    obtain ⟨preimage, membership, equality⟩ := onto value.property
    exact ⟨⟨preimage, membership⟩, Subtype.ext equality⟩
  have step (value : {value // value ∈ family}) (threshold : ℝ) :
      (independentInnovationLaw rule p positive belowOne fixedPoint).real
        {marks | (upper - (successor value).val) marks ≤ threshold} ≤
      thinningMap rule.network p ((independentInnovationLaw rule p positive belowOne fixedPoint).real
        {marks | (upper - value.val) marks ≤ ((rule.edges : ℝ)*growth)*threshold}) := by
    have gapOrder := normalizedElectricalTransferLp_gap_le_successor_gap rule p positive belowOne fixedPoint
      growth growthPositive.le upper value.val (familyNonnegative value.val value.property)
      (upperBound value.val value.property) upperFixed
    have inclusion : {marks | (upper - (successor value).val) marks ≤ threshold} ≤ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
        {marks | normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth (upper - value.val) marks ≤ threshold} := by
      filter_upwards [(Lp.coeFn_le _ _).mpr gapOrder] with marks comparison small
      exact comparison.trans small
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae inclusion)).trans
      (normalizedElectricalTransferLp_smallBall_le_thinning_all rule p positive belowOne fixedPoint growth growthPositive (upper - value.val) threshold)
  obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (classical.connected _)
  have edgesPositive : (0 : ℝ) < rule.edges := by exact_mod_cast Nat.zero_lt_of_lt edge.isLt
  have tail := IGSIII.Chemical.SmallBall.invariant_family_thinning_tail_bound rule.network
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (fun value : {value // value ∈ family} => ⇑(upper - value.val)) successor successorOnto
    positive belowOne fixedPoint classical.scale startNonnegative startBelowOne
    (mul_pos edgesPositive growthPositive) initial step
  exact ⟨gap/2, start, div_pos gapPositive (by norm_num), startNonnegative, startBelowOne,
    fun value membership depth => tail depth ⟨value, membership⟩⟩

theorem exists_uniform_invariant_electrical_gap_inverse_moments (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthAboveOne : 1 < growth)
    (family : Set (Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)))
    (compact : IsCompact family) (familyNonnegative : ∀ value ∈ family, 0 ≤ value)
    (mapsTo : Set.MapsTo (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth) family family)
    (onto : Set.SurjOn (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth) family family)
    (upper : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (upperFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth upper = upper)
    (upperBound : ∀ value ∈ family, value ≤ upper) (absent : upper ∉ family) (power : ℕ) :
    ∃ bound : ℝ, ∀ value ∈ family,
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < (upper - value) marks) ∧
      Integrable (fun marks => ((upper - value) marks)⁻¹^power)
        (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (∫ marks, ((upper - value) marks)⁻¹^power ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
  have growthPositive := zero_lt_one.trans growthAboveOne
  obtain ⟨cutoff, start, cutoffPositive, startNonnegative, startBelowOne, tail⟩ :=
    exists_uniform_invariant_electrical_gap_thinning rule classical p positive belowOne fixedPoint growth growthPositive
      family compact familyNonnegative mapsTo onto upper upperFixed upperBound absent
  obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (classical.connected _)
  have edgesAtLeastOne : (1 : ℝ) ≤ rule.edges := by exact_mod_cast Nat.zero_lt_of_lt edge.isLt
  have baseAboveOne : 1 < (rule.edges : ℝ)*growth := by nlinarith
  have cutoffs := IGSIII.Chemical.SmallBall.exists_uniform_smallBall_cutoff_of_thinning_bound rule.network
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (fun value : {value // value ∈ family} => ⇑(upper - value.val))
    positive belowOne fixedPoint classical.scale startNonnegative startBelowOne
    (zero_lt_one.trans baseAboveOne) cutoffPositive
    (fun value depth => tail value.val value.property depth)
  refine ⟨cutoff⁻¹^power * (1 + ((rule.edges : ℝ)*growth)^power *
    ∑' depth : ℕ, (((rule.edges : ℝ)*growth)^power)^depth * (thinningMap rule.network p)^[depth] start), ?_⟩
  intro value membership
  have realZero : (independentInnovationLaw rule p positive belowOne fixedPoint).real
      {marks | (upper - value) marks ≤ 0} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    apply le_of_forall_pos_le_add
    intro error errorPositive
    obtain ⟨threshold, thresholdPositive, small⟩ := cutoffs error errorPositive
    simpa only [zero_add] using (measureReal_mono (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
      (show {marks | (upper - value) marks ≤ 0} ⊆ {marks | (upper - value) marks ≤ threshold} from
        fun _ comparison => comparison.trans thresholdPositive.le)).trans (small ⟨value, membership⟩)
  have zeroMeasure : (independentInnovationLaw rule p positive belowOne fixedPoint)
      {marks | (upper - value) marks ≤ 0} = 0 := by
    exact ((ENNReal.toReal_eq_zero_iff _).mp realZero).resolve_right (measure_ne_top _ _)
  have gapPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < (upper - value) marks := by
    apply ae_iff.mpr
    simpa only [not_lt] using zeroMeasure
  obtain ⟨integrable, bound⟩ := inverse_moment_of_uniform_thinning_tail_ae rule.network
    (independentInnovationLaw rule p positive belowOne fixedPoint) power
    (Lp.stronglyMeasurable (upper - value)).measurable gapPositive positive belowOne fixedPoint classical.scale
    startNonnegative startBelowOne baseAboveOne cutoffPositive (tail value membership)
  exact ⟨gapPositive, integrable, bound⟩

end
end IGSIII34.Percolation

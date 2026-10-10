import IGSIII.Chemical.SmallBall.InvariantGapLaplace
import IGSIII.Chemical.SmallBall.InvariantGapTransfer
import IGSIII.Chemical.SmallBall.TransferThinning
import IGSIII.Probability.CompactEnvelopeGap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Set IGSIII.Probability
open scoped ENNReal

noncomputable section

theorem lp2_nonnegative_gap_second_moment_le {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (upper value : Lp ℝ 2 measure)
    (valueNonnegative : 0 ≤ value) (upperBound : value ≤ upper) :
    (∫ sample, (upper - value) sample ^ 2 ∂measure) ≤ ∫ sample, upper sample ^ 2 ∂measure := by
  apply integral_mono_ae (Lp.memLp (upper - value)).integrable_sq (Lp.memLp upper).integrable_sq
  filter_upwards [Lp.coeFn_sub upper value, (Lp.coeFn_nonneg value).mpr valueNonnegative,
    (Lp.coeFn_le value upper).mpr upperBound] with sample subtraction nonnegative comparison
  change 0 ≤ value sample at nonnegative
  rw [subtraction, Pi.sub_apply]
  nlinarith

theorem exists_uniform_invariant_gap_laplace (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (family : Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)))
    (compact : IsCompact family)
    (familyNonnegative : ∀ value ∈ family, 0 ≤ value)
    (mapsTo : Set.MapsTo (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth) family family)
    (onto : Set.SurjOn (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth) family family)
    (upper : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (upperFixed : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth upper = upper)
    (upperBound : ∀ value ∈ family, value ≤ upper) (absent : upper ∉ family)
    {target : ℝ} (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ value ∈ family,
      (∫ marks, Real.exp (-parameter * (upper - value) marks)
        ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ target := by
  obtain ⟨gap, gapPositive, meanLower⟩ := compact_order_gap_has_positive_mean family compact upper upperBound absent
  have secondBound (value : {value // value ∈ family}) :
      (∫ marks, (upper - value.val) marks ^ 2
        ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤
      max 1 (∫ marks, upper marks ^ 2 ∂independentInnovationLaw rule p positive lessOne fixedPoint) :=
    (lp2_nonnegative_gap_second_moment_le _ upper value.val
      (familyNonnegative value.val value.property) (upperBound value.val value.property)).trans (le_max_right _ _)
  obtain ⟨start, startNonnegative, startBelowOne, initial⟩ := exists_uniform_smallBall_start_of_positive_mean
    (independentInnovationLaw rule p positive lessOne fixedPoint)
    (fun value : {value // value ∈ family} => ⇑(upper - value.val))
    (fun value => (Lp.stronglyMeasurable (upper - value.val)).measurable)
    (fun value => (Lp.memLp (upper - value.val)).integrable (by norm_num))
    (fun value => (Lp.memLp (upper - value.val)).integrable_sq)
    gapPositive (zero_le_one.trans (le_max_left _ _))
    (fun value => meanLower value.val value.property) secondBound
  let successor : {value // value ∈ family} → {value // value ∈ family} := fun value =>
    ⟨normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth value.val, mapsTo value.property⟩
  have successorOnto : Function.Surjective successor := by
    intro value
    obtain ⟨preimage, membership, equality⟩ := onto value.property
    refine ⟨⟨preimage, membership⟩, ?_⟩
    apply Subtype.ext
    exact equality
  have gapNonnegative (value : {value // value ∈ family}) : 0 ≤ upper - value.val :=
    sub_nonneg.mpr (upperBound value.val value.property)
  have step (value : {value // value ∈ family}) (threshold : ℝ) :
      (independentInnovationLaw rule p positive lessOne fixedPoint).real
        {marks | (upper - (successor value).val) marks ≤ threshold} ≤
      thinningMap rule.network p
        ((independentInnovationLaw rule p positive lessOne fixedPoint).real
          {marks | (upper - value.val) marks ≤ growth * threshold}) := by
    have gapOrder := normalizedChemicalTransferLp_gap_le_successor_gap rule p positive lessOne fixedPoint
      growth growthPositive.le upper value.val upperFixed
    have inclusion : {marks | (upper - (successor value).val) marks ≤ threshold} ≤ᵐ[
        independentInnovationLaw rule p positive lessOne fixedPoint]
        {marks | normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth (upper - value.val) marks ≤ threshold} := by
      filter_upwards [(Lp.coeFn_le _ _).mpr gapOrder] with marks comparison small
      exact comparison.trans small
    have comparison := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae inclusion)
    exact comparison.trans (normalizedChemicalTransferLp_smallBall_le_thinning rule classical p positive lessOne fixedPoint
      growth growthPositive (upper - value.val) (gapNonnegative value) threshold)
  obtain ⟨parameter, parameterPositive, valid⟩ := exists_uniform_laplace_bound_of_invariant_thinning
    rule.network (independentInnovationLaw rule p positive lessOne fixedPoint)
    (fun value : {value // value ∈ family} => ⇑(upper - value.val))
    (fun value => (Lp.stronglyMeasurable (upper - value.val)).measurable)
    (fun value => (Lp.coeFn_nonneg (upper - value.val)).mpr (gapNonnegative value))
    successor successorOnto positive lessOne fixedPoint classical.scale startNonnegative startBelowOne
    growthPositive (div_pos gapPositive (by norm_num)) initial step targetPositive
  exact ⟨parameter, parameterPositive, fun value membership => valid ⟨value, membership⟩⟩

end
end IGSIII.Chemical.SmallBall

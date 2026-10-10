import IGSIII34.Percolation.ElectricalFixedLaw
import IGSIII34.Percolation.SmallBallLaw
import IGSIII.Chemical.SmallBall.ChemicalInvariantGapLaplace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal NNReal

theorem normalizedElectricalTransferLp_coe_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) (growth : ℝ)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    ⇑(normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth value) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => growth⁻¹*nonnegativeElectricalTransfer rule value marks := by
  filter_upwards [Lp.coeFn_smul growth⁻¹ (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order value),
    nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order value]
    with marks scalarEquality transferEquality
  change (growth⁻¹ • nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order value) marks = _
  simp only [scalarEquality, transferEquality, Pi.smul_apply, smul_eq_mul]

theorem normalizedElectricalTransferLp_superadditive (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth first +
      normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth second ≤
      normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth (first + second) := by
  have childNonnegative (edge : Fin rule.edges) :=
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae
      ((Lp.coeFn_nonneg first).mpr firstNonnegative |>.and ((Lp.coeFn_nonneg second).mpr secondNonnegative))
  have childAdd (edge : Fin rule.edges) :=
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae
      (Lp.coeFn_add first second)
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [normalizedElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 growth first,
    normalizedElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 growth second,
    normalizedElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 growth (first + second),
    Lp.coeFn_add (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth first)
      (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth second),
    ae_all_iff.mpr childNonnegative, ae_all_iff.mpr childAdd]
    with marks firstEquality secondEquality sumEquality addEquality nonnegative addition
  rw [addEquality, Pi.add_apply, firstEquality, secondEquality, sumEquality]
  unfold nonnegativeElectricalTransfer electricalTransfer
  have firstClip (edge : Fin rule.edges) : max (first (innovationTreeShift rule [edge] marks)) 0 =
      first (innovationTreeShift rule [edge] marks) := max_eq_left (nonnegative edge).1
  have secondClip (edge : Fin rule.edges) : max (second (innovationTreeShift rule [edge] marks)) 0 =
      second (innovationTreeShift rule [edge] marks) := max_eq_left (nonnegative edge).2
  have sumClip (edge : Fin rule.edges) : max ((first + second) (innovationTreeShift rule [edge] marks)) 0 =
      first (innovationTreeShift rule [edge] marks) + second (innovationTreeShift rule [edge] marks) := by
    rw [addition edge, Pi.add_apply, max_eq_left (add_nonneg (nonnegative edge).1 (nonnegative edge).2)]
  simp_rw [firstClip, secondClip, sumClip]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (electricalCell_superadditive rule.network (marks ([], true))
      (fun edge => (nonnegative edge).1) (fun edge => (nonnegative edge).2)) (inv_nonneg.mpr growthNonnegative)

theorem normalizedElectricalTransferLp_gap_le_successor_gap (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (upper value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueNonnegative : 0 ≤ value) (valueUpper : value ≤ upper)
    (upperFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth upper = upper) :
    normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth (upper - value) ≤
      upper - normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value := by
  apply le_sub_iff_add_le.mpr
  have bound := normalizedElectricalTransferLp_superadditive rule p positive belowOne fixedPoint
    growth growthNonnegative (upper - value) value (sub_nonneg.mpr valueUpper) valueNonnegative
  simpa only [sub_add_cancel, upperFixed] using bound

theorem electricalFixedLaw_threshold (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (threshold : ℝ) (thresholdNonnegative : 0 ≤ threshold) :
    (electricalFixedLaw rule p positive belowOne fixedPoint value : Measure ℝ≥0)
      {sample | (sample : ℝ) ≤ threshold} =
      (independentInnovationLaw rule p positive belowOne fixedPoint) {marks | value marks ≤ threshold} := by
  rw [electricalFixedLaw_measure, Measure.map_apply
    (Lp.stronglyMeasurable value).measurable.real_toNNReal
    (measurableSet_le NNReal.continuous_coe.measurable measurable_const)]
  congr 1
  ext marks
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.coe_toNNReal', max_le_iff, and_iff_left thresholdNonnegative]

theorem normalizedElectricalTransferLp_smallBall_le_thinning (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (threshold : ℝ) (thresholdNonnegative : 0 ≤ threshold) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).real
      {marks | normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value marks ≤ threshold} ≤
      thinningMap rule.network p ((independentInnovationLaw rule p positive belowOne fixedPoint).real
        {marks | value marks ≤ ((rule.edges : ℝ)*growth)*threshold}) := by
  have law := innovationTree_electrical_law rule p positive belowOne fixedPoint
    (fun marks => Real.toNNReal (value marks)) (Lp.stronglyMeasurable value).measurable.real_toNNReal
    (electricalFixedLaw rule p positive belowOne fixedPoint value) rfl
  have rootMeasurable : Measurable (fun marks => electricalCellNNReal rule.network (marks ([], true))
      (fun edge => Real.toNNReal (value (innovationTreeShift rule [edge] marks)))) :=
    (electricalCellNNReal_joint_continuous rule.network).measurable.comp
      ((measurable_pi_apply ([], true)).prodMk
        (measurable_pi_lambda _ (fun edge => (Lp.stronglyMeasurable value).measurable.real_toNNReal.comp
          (innovationTreeShift_measurable rule [edge]))))
  have eventEquality : (independentInnovationLaw rule p positive belowOne fixedPoint)
      {marks | normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value marks ≤ threshold} =
      (electricalOutputLaw rule p positive belowOne fixedPoint (electricalFixedLaw rule p positive belowOne fixedPoint value) : Measure ℝ≥0)
        {sample | (sample : ℝ) ≤ growth*threshold} := by
    rw [← law, Measure.map_apply rootMeasurable (measurableSet_le NNReal.continuous_coe.measurable measurable_const)]
    apply measure_congr
    filter_upwards [normalizedElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 growth value]
      with marks equality
    apply propext
    change (_ ≤ threshold) ↔ electricalCell rule.network (marks ([], true))
      (fun edge => ((Real.toNNReal (value (innovationTreeShift rule [edge] marks)) : ℝ≥0) : ℝ)) ≤ growth*threshold
    simp_rw [Real.coe_toNNReal']
    rw [equality, inv_mul_le_iff₀ growthPositive]
    rfl
  have bound := electricalOutputLaw_smallBall_le rule p positive belowOne fixedPoint
    (electricalFixedLaw rule p positive belowOne fixedPoint value) (growth*threshold)
    (mul_nonneg growthPositive.le thresholdNonnegative)
  rw [electricalFixedLaw_threshold rule p positive belowOne fixedPoint value _
    (mul_nonneg (Nat.cast_nonneg rule.edges) (mul_nonneg growthPositive.le thresholdNonnegative))] at bound
  have realBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
  have mapNonnegative : 0 ≤ thinningMap rule.network p
      ((independentInnovationLaw rule p positive belowOne fixedPoint).real
        {marks | value marks ≤ (rule.edges : ℝ)*(growth*threshold)}) :=
    thinningMap_nonnegative rule.network positive belowOne measureReal_nonneg measureReal_le_one
  change 0 ≤ rule.network.reliability (p*((independentInnovationLaw rule p positive belowOne fixedPoint)
    {marks | value marks ≤ (rule.edges : ℝ)*(growth*threshold)}).toReal)/p at mapNonnegative
  rw [ENNReal.toReal_ofReal mapNonnegative] at realBound
  simpa only [Measure.real_def, eventEquality, thinningMap, mul_assoc] using realBound

theorem normalizedElectricalTransferLp_nonnegative (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    0 ≤ normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [normalizedElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint 2 growth value]
    with marks equality
  rw [equality]
  exact mul_nonneg (inv_nonneg.mpr growthNonnegative)
    (electricalTransfer_nonnegative rule (fun sample => max (value sample) 0) (fun _ => le_max_right _ _) marks)

theorem normalizedElectricalTransferLp_smallBall_le_thinning_all (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)) (threshold : ℝ) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).real
      {marks | normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value marks ≤ threshold} ≤
      thinningMap rule.network p ((independentInnovationLaw rule p positive belowOne fixedPoint).real
        {marks | value marks ≤ ((rule.edges : ℝ)*growth)*threshold}) := by
  by_cases nonnegative : 0 ≤ threshold
  · exact normalizedElectricalTransferLp_smallBall_le_thinning rule p positive belowOne fixedPoint growth growthPositive value threshold nonnegative
  · have zeroMeasure : (independentInnovationLaw rule p positive belowOne fixedPoint)
        {marks | normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value marks ≤ threshold} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [(Lp.coeFn_nonneg _).mpr
        (normalizedElectricalTransferLp_nonnegative rule p positive belowOne fixedPoint growth growthPositive.le value)]
        with marks valueNonnegative
      exact not_le_of_gt ((lt_of_not_ge nonnegative).trans_le valueNonnegative)
    rw [Measure.real_def, zeroMeasure, ENNReal.toReal_zero]
    exact thinningMap_nonnegative rule.network positive belowOne measureReal_nonneg measureReal_le_one

end
end IGSIII34.Percolation

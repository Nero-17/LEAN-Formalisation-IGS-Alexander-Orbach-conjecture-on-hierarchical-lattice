import IGSIII34.Percolation.MarkingLaw
import IGSIII34.Percolation.ZeroConfiguration
import IGSIII34.Percolation.WeightedPivotal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped NNReal ENNReal

def resistanceThresholdMark (threshold : ℝ) (value : ℝ≥0) : Bool := decide ((value : ℝ) ≤ threshold)

theorem resistanceThresholdMark_measurable (threshold : ℝ) : Measurable (resistanceThresholdMark threshold) := by
  apply measurable_to_bool
  change MeasurableSet {value : ℝ≥0 | decide ((value : ℝ) ≤ threshold) = true}
  simpa only [decide_eq_true_eq] using measurableSet_le NNReal.continuous_coe.measurable measurable_const

theorem electricalInputLaw_crosses (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) :
    ∀ᵐ data ∂(electricalInputLaw rule parameter positive belowOne fixedPoint law :
      Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))), rule.network.crosses data.1 = true := by
  have preserving : MeasurePreserving Prod.fst
      (electricalInputLaw rule parameter positive belowOne fixedPoint law :
        Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0)))
      (connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _) := measurePreserving_fst
  exact preserving.quasiMeasurePreserving.ae
    (connectedConfigurationLaw_crosses rule parameter positive belowOne fixedPoint)

theorem electricalOutputLaw_smallBall_le (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) (bound : ℝ) (boundNonnegative : 0 ≤ bound) :
    (electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)
      {value | (value : ℝ) ≤ bound} ≤
        ENNReal.ofReal (rule.network.reliability
          (parameter * ((law : Measure ℝ≥0) {value | (value : ℝ) ≤ (rule.edges : ℝ) * bound}).toReal) / parameter) := by
  have thresholdMeasurable := resistanceThresholdMark_measurable ((rule.edges : ℝ) * bound)
  have markingIdentity := conditioned_iid_marking_lintegral rule parameter positive belowOne fixedPoint law
    (resistanceThresholdMark ((rule.edges : ℝ) * bound)) thresholdMeasurable
  have markEvent : {value : ℝ≥0 | resistanceThresholdMark ((rule.edges : ℝ) * bound) value = true} =
      {value : ℝ≥0 | (value : ℝ) ≤ (rule.edges : ℝ) * bound} := by
    ext value
    simp only [Set.mem_setOf_eq, resistanceThresholdMark, decide_eq_true_eq]
  rw [markEvent] at markingIdentity
  rw [← markingIdentity]
  change ((electricalInputLaw rule parameter positive belowOne fixedPoint law :
    Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
      (fun data => electricalCellNNReal rule.network data.1 data.2)) {value | (value : ℝ) ≤ bound} ≤ _
  rw [Measure.map_apply (electricalCellNNReal_joint_continuous rule.network).measurable
    (measurableSet_le NNReal.continuous_coe.measurable measurable_const)]
  have eventMeasurable : MeasurableSet {data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) |
      ((electricalCellNNReal rule.network data.1 data.2 : ℝ≥0) : ℝ) ≤ bound} :=
    measurableSet_le (NNReal.continuous_coe.comp
      (electricalCellNNReal_joint_continuous rule.network)).measurable measurable_const
  change (electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _)
    {data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) |
      ((electricalCellNNReal rule.network data.1 data.2 : ℝ≥0) : ℝ) ≤ bound} ≤ _
  rw [← lintegral_indicator_one (μ := (electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _))
    (s := {data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) |
    ((electricalCellNNReal rule.network data.1 data.2 : ℝ≥0) : ℝ) ≤ bound}) eventMeasurable]
  apply lintegral_mono_ae
  filter_upwards [electricalInputLaw_crosses rule parameter positive belowOne fixedPoint law] with data crossing
  change (if ((electricalCellNNReal rule.network data.1 data.2 : ℝ≥0) : ℝ) ≤ bound then 1 else 0 : ℝ≥0∞) ≤ _
  by_cases resistanceSmall : ((electricalCellNNReal rule.network data.1 data.2 : ℝ≥0) : ℝ) ≤ bound
  · have thinnedCrossing : rule.network.crosses (smallConfiguration data.1
        (fun edge => (data.2 edge : ℝ)) ((rule.edges : ℝ) * bound)) = true := by
      rcases boundNonnegative.eq_or_lt with zero | boundPositive
      · have zeroResistance : electricalCell rule.network data.1 (fun edge => (data.2 edge : ℝ)) = 0 := by
          have nonnegative : 0 ≤ electricalCell rule.network data.1 (fun edge => (data.2 edge : ℝ)) :=
            (electricalCellNNReal rule.network data.1 data.2).property
          change electricalCell rule.network data.1 (fun edge => (data.2 edge : ℝ)) ≤ bound at resistanceSmall
          linarith
        have thresholdZero : (rule.edges : ℝ) * bound = 0 := by rw [← zero, mul_zero]
        rw [thresholdZero]
        exact electricalCell_zeroConfiguration_crosses rule.network data.1 crossing
          (fun edge => (data.2 edge).2) zeroResistance
      · exact electricalCell_smallConfiguration_crosses rule.network data.1 crossing
          (fun edge => (data.2 edge).2) boundPositive resistanceSmall
    change rule.network.crosses (fun edge => data.1 edge &&
      resistanceThresholdMark ((rule.edges : ℝ) * bound) (data.2 edge)) = true at thinnedCrossing
    simp only [resistanceSmall, thinnedCrossing, ↓reduceIte, le_refl]
  · simp only [resistanceSmall, ↓reduceIte, zero_le]

end
end IGSIII34.Percolation

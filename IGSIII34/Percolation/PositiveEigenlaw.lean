import IGSIII34.Percolation.SmallBallLaw
import IGSIII34.Percolation.EigenlawExistence
import Universality.Percolation.UniqueFixedPoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped NNReal ENNReal

theorem nnreal_nonpositive_set : {value : ℝ≥0 | (value : ℝ) ≤ 0} = {0} := by
  ext value
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro nonpositive
    exact le_antisymm (NNReal.coe_le_coe.mp nonpositive) zero_le
  · rintro rfl
    exact le_rfl

theorem scaledProbabilityLaw_zero_mass (scalar : ℝ≥0) (scalarNonzero : scalar ≠ 0)
    (law : ProbabilityMeasure ℝ≥0) :
    (scaledProbabilityLaw scalar law : Measure ℝ≥0) {0} = (law : Measure ℝ≥0) {0} := by
  rw [scaledProbabilityLaw_measure, Measure.map_apply (f := fun value : ℝ≥0 => scalar * value)
    (measurable_const.mul measurable_id)
    (measurableSet_singleton _)]
  congr 1
  ext value
  simp only [Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero, scalarNonzero, false_or]

theorem meanOneLaw_zero_mass_ne_one (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1) :
    (law : Measure ℝ≥0) {0} ≠ 1 := by
  intro zeroMassOne
  have almostZero : ∀ᵐ value ∂(law : Measure ℝ≥0), value = 0 := by
    apply ae_iff.mpr
    change (law : Measure ℝ≥0) ({0} : Set ℝ≥0)ᶜ = 0
    rw [measure_compl (measurableSet_singleton _) (measure_ne_top _ _), measure_univ, zeroMassOne, tsub_self]
  have meanZero : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 0 := by
    calc
      _ = ∫ _value : ℝ≥0, (0 : ℝ) ∂(law : Measure ℝ≥0) := by
        apply integral_congr_ae
        filter_upwards [almostZero] with value equality
        simp only [equality, NNReal.coe_zero]
      _ = 0 := integral_zero _ _
  linarith

theorem normalized_electrical_eigenlaw_zero_mass (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1)
    (meanPositive : 0 < electricalOutputMean rule parameter positive belowOne fixedPoint law)
    (eigenlaw : normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law) :
    (law : Measure ℝ≥0) {0} = 0 := by
  have scalarPositive : 0 < Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ :=
    Real.toNNReal_pos.mpr (inv_pos.mpr meanPositive)
  have zeroMassEquality : (electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0) {0} =
      (law : Measure ℝ≥0) {0} := by
    calc
      _ = (normalizedElectricalLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0) {0} :=
        (scaledProbabilityLaw_zero_mass _ scalarPositive.ne'
          (electricalOutputLaw rule parameter positive belowOne fixedPoint law)).symm
      _ = _ := congrArg (fun output : ProbabilityMeasure ℝ≥0 => (output : Measure ℝ≥0) {0}) eigenlaw
  have zeroBound := electricalOutputLaw_smallBall_le rule parameter positive belowOne fixedPoint law 0 le_rfl
  simp only [mul_zero, nnreal_nonpositive_set, zeroMassEquality] at zeroBound
  have zeroMassFinite : (law : Measure ℝ≥0) {0} ≠ ∞ := measure_ne_top _ _
  have retentionBounds := IGSIII34.Probability.bool_marking_probability_bounds law
    (resistanceThresholdMark 0)
  have eventEquality : {value : ℝ≥0 | resistanceThresholdMark 0 value = true} = {0} := by
    simp only [resistanceThresholdMark, decide_eq_true_eq, nnreal_nonpositive_set]
  rw [eventEquality] at retentionBounds
  by_contra massNonzero
  have retentionPositive : 0 < ((law : Measure ℝ≥0) {0}).toReal :=
    ENNReal.toReal_pos massNonzero zeroMassFinite
  have retentionBelowOne : ((law : Measure ℝ≥0) {0}).toReal < 1 := by
    apply lt_of_le_of_ne retentionBounds.2
    intro equality
    apply meanOneLaw_zero_mass_ne_one law meanOne
    rw [← ENNReal.ofReal_toReal zeroMassFinite, equality, ENNReal.ofReal_one]
  have strict := rule.network.reliability_lt_parameter_below_fixed parameter
    (parameter * ((law : Measure ℝ≥0) {0}).toReal) positive belowOne fixedPoint
    (mul_pos positive retentionPositive) (by nlinarith) classical.scale
  have probabilityStrict : rule.network.reliability
      (parameter * ((law : Measure ℝ≥0) {0}).toReal) / parameter < ((law : Measure ℝ≥0) {0}).toReal := by
    apply (div_lt_iff₀ positive).mpr
    simpa only [mul_comm] using strict
  have zeroMassRepr : (law : Measure ℝ≥0) {0} = ENNReal.ofReal ((law : Measure ℝ≥0) {0}).toReal :=
    (ENNReal.ofReal_toReal zeroMassFinite).symm
  have probabilityNonnegative : 0 ≤ rule.network.reliability
      (parameter * ((law : Measure ℝ≥0) {0}).toReal) / parameter :=
    div_nonneg (rule.network.reliability_nonneg (mul_nonneg positive.le retentionBounds.1)
      (by nlinarith [belowOne.le, retentionBounds.1, retentionBounds.2])) positive.le
  have convertedBound : ENNReal.ofReal ((law : Measure ℝ≥0) {0}).toReal ≤
      ENNReal.ofReal (rule.network.reliability
        (parameter * ((law : Measure ℝ≥0) {0}).toReal) / parameter) :=
    zeroMassRepr.symm.trans_le zeroBound
  have boundReal := (ENNReal.ofReal_le_ofReal_iff probabilityNonnegative).mp convertedBound
  linarith

theorem exists_positive_electrical_eigenlaw (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ law : ProbabilityMeasure ℝ≥0,
      (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1 ∧
      (∀ power : ℕ, (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) < ∞) ∧
      normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law ∧
      1 < electricalOutputMean rule parameter positive belowOne fixedPoint law ∧
      ∀ᵐ value ∂(law : Measure ℝ≥0), 0 < value := by
  obtain ⟨law, meanOne, moments, fixed, meanAboveOne⟩ :=
    exists_nonnegative_electrical_eigenlaw rule classical parameter positive belowOne fixedPoint
  have zeroMass := normalized_electrical_eigenlaw_zero_mass rule classical parameter positive belowOne fixedPoint
    law meanOne (zero_lt_one.trans meanAboveOne) fixed
  refine ⟨law, meanOne, moments, fixed, meanAboveOne, ?_⟩
  apply ae_iff.mpr
  have zeroSet : {value : ℝ≥0 | ¬ 0 < value} = {0} := by ext value; simp
  rw [zeroSet]
  exact zeroMass

end
end IGSIII34.Percolation

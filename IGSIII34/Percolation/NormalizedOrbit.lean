import IGSIII34.Percolation.EigenlawInterval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped NNReal ENNReal

def normalizedElectricalOrbit (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    ProbabilityMeasure ℝ≥0 :=
  (normalizedElectricalLaw rule parameter positive belowOne fixedPoint)^[depth] (diracProba (1 : ℝ≥0))

theorem normalizedElectricalOrbit_zero (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    normalizedElectricalOrbit rule parameter positive belowOne fixedPoint 0 = diracProba (1 : ℝ≥0) := rfl

theorem normalizedElectricalOrbit_succ (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    normalizedElectricalOrbit rule parameter positive belowOne fixedPoint (depth + 1) =
      normalizedElectricalLaw rule parameter positive belowOne fixedPoint
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth) :=
  Function.iterate_succ_apply' _ _ _

theorem exists_invariant_electrical_orbit_moment_family (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ lowerOrder : ℕ, 2 ≤ lowerOrder ∧ ∃ bounds : ℕ → ℝ≥0,
      ∀ depth, normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth ∈
        meanOneMomentFamily lowerOrder bounds := by
  have derivativeAboveOne := rule.network.interior_fixed_point_strictly_unstable
    parameter positive belowOne fixedPoint classical.scale
  let coefficient : ℝ≥0 := Real.toNNReal (deriv rule.network.reliability parameter)
  have coefficientEquality : (coefficient : ℝ) = deriv rule.network.reliability parameter :=
    Real.coe_toNNReal _ (zero_lt_one.trans derivativeAboveOne).le
  have coefficientAboveOne : 1 < coefficient := by
    apply NNReal.coe_lt_coe.mp
    simpa only [NNReal.coe_one, coefficientEquality] using derivativeAboveOne
  obtain ⟨lowerOrder, orderBound, bounds, boundProperties⟩ :=
    exists_all_invariant_powerMoment_bounds rule.edges coefficient coefficientAboveOne
  refine ⟨lowerOrder, orderBound, bounds, ?_⟩
  intro depth
  induction depth with
  | zero =>
    rw [normalizedElectricalOrbit_zero]
    constructor
    · change (∫ value : ℝ≥0, (value : ℝ) ∂Measure.dirac (1 : ℝ≥0)) = 1
      simp
    · intro power highOrder
      change (∫⁻ value : ℝ≥0, (value : ℝ≥0∞) ^ power ∂Measure.dirac (1 : ℝ≥0)) ≤ bounds power
      simpa only [lintegral_dirac, ENNReal.coe_one, one_pow] using
        ENNReal.coe_le_coe.mpr (boundProperties power highOrder).1
  | succ depth inductionHypothesis =>
    rw [normalizedElectricalOrbit_succ]
    exact normalizedElectricalLaw_preserves_momentFamily rule parameter positive belowOne fixedPoint
      coefficient (zero_lt_one.trans coefficientAboveOne) coefficientEquality.le
      lowerOrder orderBound bounds boundProperties _ inductionHypothesis

theorem normalizedElectricalOrbit_mean_one (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    (∫ value : ℝ≥0, (value : ℝ)
      ∂(normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0)) = 1 := by
  obtain ⟨_, _, _, member⟩ := exists_invariant_electrical_orbit_moment_family
    rule classical parameter positive belowOne fixedPoint
  exact (member depth).1

theorem normalizedElectricalOrbit_uniform_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (power : ℕ) :
    ∃ bound : ℝ≥0, ∀ depth,
      (∫⁻ value, (value : ℝ≥0∞) ^ power
        ∂(normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0)) ≤ bound := by
  obtain ⟨lowerOrder, _, bounds, member⟩ := exists_invariant_electrical_orbit_moment_family
    rule classical parameter positive belowOne fixedPoint
  refine ⟨1 + bounds (max lowerOrder power), fun depth => ?_⟩
  exact (moment_le_one_add_higherMoment _ (le_max_right lowerOrder power)).trans
    (by exact add_le_add le_rfl ((member depth).2 _ (le_max_left lowerOrder power)))

theorem electricalOutputMean_le_edgeCount (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (inputIntegrable : Integrable (fun value : ℝ≥0 => (value : ℝ)) (law : Measure ℝ≥0))
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1) :
    electricalOutputMean rule parameter positive belowOne fixedPoint law ≤ rule.edges := by
  apply (electricalOutputMean_le_conditional_unit rule parameter positive belowOne fixedPoint law
    inputIntegrable meanOne).trans
  calc
    _ ≤ ∫ _configuration : Configuration rule.edges, (rule.edges : ℝ)
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure (Configuration rule.edges)) := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro configuration
      have comparison := electricalCell_le_sum rule.network configuration (input := fun _ => (1 : ℝ))
        (fun _ => zero_le_one)
      simpa only [electricalCell, configurationResistance, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] using comparison
    _ = _ := by simp

theorem normalizedElectricalOrbit_outputMean_bounds (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    deriv rule.network.reliability parameter ≤
        electricalOutputMean rule parameter positive belowOne fixedPoint
          (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth) ∧
      electricalOutputMean rule parameter positive belowOne fixedPoint
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth) ≤ rule.edges := by
  obtain ⟨bound, boundHolds⟩ := normalizedElectricalOrbit_uniform_moment
    rule classical parameter positive belowOne fixedPoint 2
  have integrable := integrable_coe_of_secondMoment_bound _ bound (boundHolds depth)
  have meanOne := normalizedElectricalOrbit_mean_one rule classical parameter positive belowOne fixedPoint depth
  exact ⟨electricalOutputMean_pivotal_lower rule parameter positive belowOne fixedPoint _ bound
      (boundHolds depth) (lintegral_eq_one_of_mean_eq_one _ meanOne),
    electricalOutputMean_le_edgeCount rule parameter positive belowOne fixedPoint _ integrable meanOne⟩

end
end IGSIII34.Percolation

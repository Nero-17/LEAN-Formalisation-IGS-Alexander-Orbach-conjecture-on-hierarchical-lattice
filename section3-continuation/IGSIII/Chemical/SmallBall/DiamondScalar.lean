import IGSIII.Chemical.EqualLengthScalar
import IGSIII.Chemical.AddressConvergence
import Universality.Examples.DiamondCritical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution Filter IGSIII.Probability
open scoped ENNReal Topology

noncomputable section

theorem diamond_manuscript_mean_eq_pow
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : diamondRule.network.reliability p = p)
    (depth : ℕ) : manuscriptDistanceMean diamondRule p depth = (2 : ℝ) ^ depth := by
  have values : ⇑(chemicalOrbit diamondRule p positive belowOne fixedPoint 1 depth) =ᵐ[
      independentInnovationLaw diamondRule p positive belowOne fixedPoint] fun _ => (2 : ℝ) ^ depth := by
    cases depth with
    | zero => exact chemicalUnitLp_ae diamondRule p positive belowOne fixedPoint 2
    | succ depth =>
      filter_upwards [chemicalOrbit_shift_eq_terminalScaledDistance_ae diamondRule diamondRule_classical
        p positive belowOne fixedPoint 1 (by norm_num), independentInnovationLaw_crosses diamondRule p positive belowOne fixedPoint]
        with marks orbitValues crossing
      have distance := diamond_actual_crossing_distance depth (markedGenerationConfiguration diamondRule marks depth [] true)
        (markedGenerationConfiguration_crosses diamondRule marks crossing depth [] true)
      have equality := orbitValues [] depth
      change chemicalOrbit diamondRule p positive belowOne fixedPoint 1 (depth + 1) marks = _ at equality
      rw [IGSIII.Geometry.markedTerminalDistance, distance] at equality
      simpa only [one_pow, div_one, Nat.cast_pow, Nat.cast_ofNat] using equality
  have equality := integral_congr_ae values
  simpa only [chemicalOrbit_mean diamondRule diamondRule_classical p positive belowOne fixedPoint 1 (by norm_num),
    one_pow, div_one, integral_const, probReal_univ, one_smul] using equality

theorem diamond_scalar_rigidity
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : diamondRule.network.reliability p = p)
    (constant growth amplitude : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean diamondRule p depth ∧
      manuscriptDistanceMean diamondRule p depth ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw diamondRule p positive belowOne fixedPoint))
    (valueMeanOne : (∫ marks, value marks ∂independentInnovationLaw diamondRule p positive belowOne fixedPoint) = 1)
    (fieldConvergence : ∀ᵐ marks ∂independentInnovationLaw diamondRule p positive belowOne fixedPoint, ∀ address,
      Tendsto (fun depth => (IGSIII.Geometry.markedTerminalDistance diamondRule marks depth address true : ℝ) / growth ^ (depth + 1))
        atTop (𝓝 (amplitude * chemicalField diamondRule p positive belowOne fixedPoint value address marks))) :
    growth = 2 ∧ amplitude = 1 ∧
      ∀ᵐ marks ∂independentInnovationLaw diamondRule p positive belowOne fixedPoint, ∀ address,
        chemicalField diamondRule p positive belowOne fixedPoint value address marks = 1 := by
  have deterministicBounds : ∀ depth, (2 : ℝ) ^ depth ≤ manuscriptDistanceMean diamondRule p depth ∧
      manuscriptDistanceMean diamondRule p depth ≤ 1 * (2 : ℝ) ^ depth := by
    intro depth
    rw [diamond_manuscript_mean_eq_pow p positive belowOne fixedPoint depth, one_mul]
    exact ⟨le_refl _, le_refl _⟩
  have growthEquality := exponential_growth_unique (manuscriptDistanceMean diamondRule p)
    growth 2 constant⁻¹ 1 growthPositive (by norm_num) meanBounds deterministicBounds
  have productOne : ∀ᵐ marks ∂independentInnovationLaw diamondRule p positive belowOne fixedPoint, ∀ address,
      amplitude * chemicalField diamondRule p positive belowOne fixedPoint value address marks = 1 := by
    filter_upwards [fieldConvergence, independentInnovationLaw_crosses diamondRule p positive belowOne fixedPoint] with marks limits crossing
    intro address
    have sequenceOne : (fun depth => (IGSIII.Geometry.markedTerminalDistance diamondRule marks depth address true : ℝ) / growth ^ (depth + 1)) =
        fun _ : ℕ => (1 : ℝ) := by
      funext depth
      have distance := diamond_actual_crossing_distance depth (markedGenerationConfiguration diamondRule marks depth address true)
        (markedGenerationConfiguration_crosses diamondRule marks crossing depth address true)
      rw [IGSIII.Geometry.markedTerminalDistance, distance, growthEquality]
      simp only [Nat.cast_pow, Nat.cast_ofNat, div_self (by positivity : (2 : ℝ) ^ (depth + 1) ≠ 0)]
    exact tendsto_nhds_unique (limits address) (sequenceOne ▸ tendsto_const_nhds)
  have rootProduct : (fun marks => amplitude * value marks) =ᵐ[independentInnovationLaw diamondRule p positive belowOne fixedPoint]
      fun _ => (1 : ℝ) := by
    filter_upwards [productOne] with marks products
    exact products []
  have amplitudeEquality : amplitude = 1 := by
    have equality := integral_congr_ae rootProduct
    simpa only [integral_const_mul, valueMeanOne, mul_one, integral_const, probReal_univ, one_smul] using equality
  refine ⟨growthEquality, amplitudeEquality, ?_⟩
  filter_upwards [productOne] with marks products
  simpa only [amplitudeEquality, one_mul] using products

theorem exists_actual_diamond_scalar
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : diamondRule.network.reliability p = p) :
    ∃ value : Lp ℝ 2 (independentInnovationLaw diamondRule p positive belowOne fixedPoint),
      normalizedChemicalTransferLp diamondRule p positive belowOne fixedPoint 2 2 value = value ∧
      (∫ marks, value marks ∂independentInnovationLaw diamondRule p positive belowOne fixedPoint) = 1 ∧
      ∀ᵐ marks ∂independentInnovationLaw diamondRule p positive belowOne fixedPoint, ∀ address,
        chemicalField diamondRule p positive belowOne fixedPoint value address marks = 1 ∧
        Tendsto (fun depth => (IGSIII.Geometry.markedTerminalDistance diamondRule marks depth address true : ℝ) / (2 : ℝ) ^ (depth + 1))
          atTop (𝓝 1) := by
  obtain ⟨constant, growth, _, _, growthLower, _, meanBounds, value, valueFixed, _, valueMean,
    amplitude, _, fieldLimits, _, _, _, _⟩ := exists_actual_chemical_scalar diamondRule diamondRule_classical p positive belowOne fixedPoint
  have growthPositive : 0 < growth :=
    (show (0 : ℝ) < (diamondRule.network.fullGraph.dist diamondRule.network.source diamondRule.network.target : ℝ) by
      rw [show diamondRule.network = diamondNetwork from rfl, diamond_terminal_distance]
      norm_num).trans_le growthLower
  have rigidity := diamond_scalar_rigidity p positive belowOne fixedPoint constant growth amplitude growthPositive meanBounds value valueMean
    (fieldLimits.mono (fun _ fields address => (fields address).2.2))
  refine ⟨value, ?_, valueMean, ?_⟩
  · simpa only [rigidity.1] using valueFixed
  · filter_upwards [rigidity.2.2, fieldLimits] with marks values limits
    intro address
    refine ⟨values address, ?_⟩
    simpa only [rigidity.1, rigidity.2.1, values address, one_mul] using (limits address).2.2

theorem diamond_critical_manuscript_mean (depth : ℕ) :
    manuscriptDistanceMean diamondRule diamondCriticalProbability depth = (2 : ℝ) ^ depth :=
  diamond_manuscript_mean_eq_pow diamondCriticalProbability diamond_critical_probability_bounds.1
    diamond_critical_probability_bounds.2 diamond_critical_fixed_point depth

theorem exists_actual_diamond_critical_scalar :
    ∃ value : Lp ℝ 2 (independentInnovationLaw diamondRule diamondCriticalProbability
        diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2 diamond_critical_fixed_point),
      normalizedChemicalTransferLp diamondRule diamondCriticalProbability
        diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2 diamond_critical_fixed_point 2 2 value = value ∧
      (∫ marks, value marks ∂independentInnovationLaw diamondRule diamondCriticalProbability
        diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2 diamond_critical_fixed_point) = 1 ∧
      ∀ᵐ marks ∂independentInnovationLaw diamondRule diamondCriticalProbability
        diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2 diamond_critical_fixed_point, ∀ address,
        chemicalField diamondRule diamondCriticalProbability diamond_critical_probability_bounds.1
          diamond_critical_probability_bounds.2 diamond_critical_fixed_point value address marks = 1 ∧
        Tendsto (fun depth => (IGSIII.Geometry.markedTerminalDistance diamondRule marks depth address true : ℝ) / (2 : ℝ) ^ (depth + 1))
          atTop (𝓝 1) :=
  exists_actual_diamond_scalar diamondCriticalProbability diamond_critical_probability_bounds.1
    diamond_critical_probability_bounds.2 diamond_critical_fixed_point
end
end IGSIII.Chemical.SmallBall
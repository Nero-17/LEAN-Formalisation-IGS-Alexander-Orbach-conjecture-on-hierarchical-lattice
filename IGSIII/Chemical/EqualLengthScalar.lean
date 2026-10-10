import IGSIII.Chemical.ChemicalScalar
import IGSIII.Chemical.EqualLengthActual
import IGSIII.Probability.ExponentialGrowthUniqueness

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter IGSIII.Chemical.SmallBall IGSIII.Probability
open scoped Topology ENNReal

theorem manuscript_mean_eq_pow_of_equal_paths
    (rule : Rule) (classicalRule : rule.Classical) (length : ℕ)
    (equalLengths : ∀ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
      walk.IsPath → walk.length = length)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) : manuscriptDistanceMean rule p depth = (length : ℝ) ^ depth := by
  have values : ⇑(chemicalOrbit rule p positive belowOne fixedPoint 1 depth) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] fun _ => (length : ℝ) ^ depth := by
    filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
      normalizedChemicalTransferLp_iterate_ae rule p positive belowOne fixedPoint 2 1 (by norm_num) depth]
      with marks crossing iterateEquality
    change _ = _ at iterateEquality
    have rootShift : innovationTreeShift rule [] marks = marks := rfl
    have pathEquality := chemicalTransfer_unit_iterate_eq_pow_of_equal_paths rule classicalRule length equalLengths marks crossing depth []
    rw [rootShift] at pathEquality
    rw [pathEquality] at iterateEquality
    simpa only [chemicalOrbit, inv_one, one_pow, one_mul] using iterateEquality
  have equality := integral_congr_ae values
  simpa only [chemicalOrbit_mean rule classicalRule p positive belowOne fixedPoint 1 (by norm_num),
    one_pow, div_one, integral_const, probReal_univ, one_smul] using equality

theorem equal_paths_scalar_rigidity
    (rule : Rule) (classicalRule : rule.Classical) (length : ℕ) (lengthPositive : 0 < length)
    (equalLengths : ∀ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
      walk.IsPath → walk.length = length)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth amplitude : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueMeanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (fieldConvergence : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
      Tendsto (fun depth => (IGSIII.Geometry.markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
        atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks))) :
    growth = length ∧ amplitude = 1 ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
        chemicalField rule p positive belowOne fixedPoint value address marks = 1 := by
  have deterministicBounds : ∀ depth, (length : ℝ) ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ 1 * (length : ℝ) ^ depth := by
    intro depth
    rw [manuscript_mean_eq_pow_of_equal_paths rule classicalRule length equalLengths p positive belowOne fixedPoint depth, one_mul]
    exact ⟨le_refl _, le_refl _⟩
  have growthEquality := IGSIII.Probability.exponential_growth_unique (manuscriptDistanceMean rule p)
    growth length constant⁻¹ 1 growthPositive (by exact_mod_cast lengthPositive) meanBounds deterministicBounds
  have productOne : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
      amplitude * chemicalField rule p positive belowOne fixedPoint value address marks = 1 := by
    filter_upwards [fieldConvergence, independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks limits crossing
    intro address
    have sequenceOne : (fun depth => (IGSIII.Geometry.markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1)) =
        fun _ : ℕ => (1 : ℝ) := by
      funext depth
      rw [IGSIII.Geometry.markedTerminalDistance, actual_marked_distance_eq_pow_of_equal_paths rule classicalRule length equalLengths marks crossing,
        growthEquality, div_self (pow_pos (by exact_mod_cast lengthPositive : (0 : ℝ) < length) _).ne']
    exact tendsto_nhds_unique (limits address) (sequenceOne ▸ tendsto_const_nhds)
  have rootProduct : (fun marks => amplitude * value marks) =ᵐ[independentInnovationLaw rule p positive belowOne fixedPoint]
      fun _ => (1 : ℝ) := by
    filter_upwards [productOne] with marks products
    exact products []
  have amplitudeEquality : amplitude = 1 := by
    have equality := integral_congr_ae rootProduct
    simpa only [integral_const_mul, valueMeanOne, mul_one, integral_const, probReal_univ, one_smul] using equality
  refine ⟨growthEquality, amplitudeEquality, ?_⟩
  filter_upwards [productOne] with marks products
  simpa only [amplitudeEquality, one_mul] using products

theorem equal_terminal_path_length_eq_distance (rule : Rule) (classicalRule : rule.Classical) (length : ℕ)
    (equalLengths : ∀ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
      walk.IsPath → walk.length = length) :
    length = rule.network.fullGraph.dist rule.network.source rule.network.target := by
  obtain ⟨walk, path, lengthIdentity⟩ := (classicalRule.connected rule.network.target).exists_path_of_dist
  exact (equalLengths walk path).symm.trans lengthIdentity

theorem exists_actual_equal_length_scalar (rule : Rule) (classicalRule : rule.Classical)
    (equalLengths : ∀ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
      walk.IsPath → walk.length = rule.network.fullGraph.dist rule.network.source rule.network.target)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
      normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2
        (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) value = value ∧
      (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
        chemicalField rule p positive belowOne fixedPoint value address marks = 1 := by
  obtain ⟨constant, growth, _, _, growthLower, _, meanBounds, value, valueFixed, _, valueMean,
    amplitude, _, fieldLimits, _, _, _, _⟩ := exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  have lengthPositive := Nat.zero_lt_of_lt classicalRule.scale
  have growthPositive : 0 < growth :=
    (show (0 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by exact_mod_cast lengthPositive).trans_le growthLower
  have rigidity := equal_paths_scalar_rigidity rule classicalRule _ lengthPositive equalLengths p positive belowOne fixedPoint
    constant growth amplitude growthPositive meanBounds value valueMean (fieldLimits.mono (fun _ fields address => (fields address).2.2))
  refine ⟨value, ?_, valueMean, rigidity.2.2⟩
  simpa only [rigidity.1] using valueFixed

end IGSIII.Chemical.Substitution

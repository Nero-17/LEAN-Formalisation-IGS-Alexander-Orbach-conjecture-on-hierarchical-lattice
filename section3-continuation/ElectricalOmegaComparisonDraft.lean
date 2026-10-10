import IGSIII34.Percolation.ElectricalGrowthResidual
import IGSIII34.Percolation.ElectricalOmega
import IGSIII34.Percolation.GenerationRealMoments
import IGSIII34.Probability.OrderedApproximations

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped _root_.Topology ENNReal

theorem markedElectricalBlockMean_pairwise_le
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (inverseMoment : ℝ) (inverseAtLeastOne : 1 ≤ inverseMoment)
    (inverseBound : ∀ depth, finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)⁻¹) ≤ inverseMoment)
    (constantPositive : 0 < constant) (coarse firstFine secondFine : ℕ) (address : List (Fin rule.edges)) :
    markedObservableLp rule p positive belowOne fixedPoint coarse address true
        (generationElectricalBlockMean rule p growth coarse firstFine) ≤
      (inverseMoment*constant⁻¹) • markedObservableLp rule p positive belowOne fixedPoint coarse address true
        (generationElectricalBlockMean rule p growth coarse secondFine) := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [markedObservableLp_ae rule p positive belowOne fixedPoint coarse address true
      (generationElectricalBlockMean rule p growth coarse firstFine),
    markedObservableLp_ae rule p positive belowOne fixedPoint coarse address true
      (generationElectricalBlockMean rule p growth coarse secondFine),
    Lp.coeFn_smul (inverseMoment*constant⁻¹) (markedObservableLp rule p positive belowOne fixedPoint coarse address true
      (generationElectricalBlockMean rule p growth coarse secondFine))] with marks firstEquality secondEquality scalarEquality
  rw [firstEquality, scalarEquality, Pi.smul_apply, smul_eq_mul, secondEquality]
  exact generationElectricalBlockMean_pairwise_le rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds inverseMoment inverseAtLeastOne inverseBound constantPositive coarse firstFine secondFine _

theorem electricalOmega_pairwise_le_of_moments
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (constantPositive : 0 < constant)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (powerContracts : (rule.edges : ℝ)^(1/power) < deriv rule.network.reliability p)
    (secondMoment inversePowerMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inversePowerMomentNonnegative : 0 ≤ inversePowerMoment)
    (secondMomentBound : ∀ depth, finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)^2) ≤ secondMoment)
    (inversePowerBound : ∀ depth, finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)⁻¹^power) ≤ inversePowerMoment)
    (inverseMoment : ℝ) (inverseAtLeastOne : 1 ≤ inverseMoment)
    (inverseBound : ∀ depth, finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)⁻¹) ≤ inverseMoment)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (firstMember : first ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (secondMember : second ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    first ≤ (inverseMoment*constant⁻¹) • second := by
  have derivativePositive := zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
    p positive belowOne fixedPoint classical.scale)
  have ratioNonnegative : 0 ≤ (rule.edges : ℝ)^(1/power)/deriv rule.network.reliability p :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) derivativePositive.le
  have ratioLessOne : (rule.edges : ℝ)^(1/power)/deriv rule.network.reliability p < 1 :=
    (div_lt_one derivativePositive).mpr powerContracts
  apply IGSIII34.Probability.orbitClusterSet_pairwise_le_of_ordered_approximations
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (electricalOrbitLp rule p positive belowOne fixedPoint growth)
    (fun coarse depth => markedObservableLp rule p positive belowOne fixedPoint coarse [] true
      (generationElectricalBlockMean rule p growth coarse (depth-coarse-2)))
    (fun coarse => constant⁻¹*Real.sqrt ((2*secondMoment*Real.sqrt secondMoment*inversePowerMoment^(1/power))*
      (((rule.edges : ℝ)^(1/power))/deriv rule.network.reliability p)^(coarse+1)))
    ?_ (inverseMoment*constant⁻¹) ?_ ?_ first second firstMember secondMember
  · have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioLessOne
    have shifted := geometric.mul_const ((rule.edges : ℝ)^(1/power)/deriv rule.network.reliability p)
    have scaled := shifted.const_mul (2*secondMoment*Real.sqrt secondMoment*inversePowerMoment^(1/power))
    have rooted := Real.continuous_sqrt.continuousAt.tendsto.comp scaled
    simpa only [Function.comp_def, pow_succ, mul_zero, zero_mul, Real.sqrt_zero] using rooted.const_mul constant⁻¹
  · intro coarse depth large
    have identity := electricalOrbitLp_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthPositive.le
      (coarse+(depth-coarse-2)+1)
    rw [show coarse+(depth-coarse-2)+1+1 = depth by omega] at identity
    rw [identity]
    exact marked_growth_electrical_residual_geometric rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds [] coarse (depth-coarse-2)
      powerAtLeastTwo secondMoment inversePowerMoment secondMomentNonnegative inversePowerMomentNonnegative
      secondMomentBound (inversePowerBound _)
  · intro coarse firstDepth secondDepth _ _
    exact markedElectricalBlockMean_pairwise_le rule classical p positive belowOne fixedPoint
      constant growth growthPositive growthBounds inverseMoment inverseAtLeastOne inverseBound constantPositive
      coarse (firstDepth-coarse-2) (secondDepth-coarse-2) []

theorem exists_uniform_electricalOmega_pairwise_comparison
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)
    (constantPositive : 0 < constant) :
    ∃ comparisonConstant : ℝ, 1 ≤ comparisonConstant ∧
      ∀ first ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
        ∀ second ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
          first ≤ comparisonConstant • second := by
  obtain ⟨power, powerAtLeastTwo, powerContracts⟩ := exists_inverse_power_contracting (rule.edges : ℝ)
    (deriv rule.network.reliability p)
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale)
  obtain ⟨secondMoment, secondAtLeastOne, secondBound⟩ :=
    generation_normalizedResistance_uniform_second_moment rule classical p positive belowOne fixedPoint
  obtain ⟨inversePowerMoment, inversePowerAtLeastOne, inversePowerBound⟩ :=
    generation_normalizedResistance_uniform_real_inverse_moment rule classical p positive belowOne fixedPoint power
  obtain ⟨inverseMoment, inverseAtLeastOne, inverseBound⟩ :=
    generation_normalizedResistance_uniform_inverse_moment rule classical p positive belowOne fixedPoint
  have inverseConstantAtLeastOne : 1 ≤ constant⁻¹ := by
    simpa only [electricalOrbitScale, NNReal.coe_one, pow_zero, mul_one] using (growthBounds 0).2
  refine ⟨inverseMoment*constant⁻¹, ?_, fun first firstMember second secondMember => ?_⟩
  · simpa only [one_mul] using mul_le_mul inverseAtLeastOne inverseConstantAtLeastOne
      zero_le_one (zero_le_one.trans inverseAtLeastOne)
  · exact electricalOmega_pairwise_le_of_moments rule classical p positive belowOne fixedPoint
      constant growth growthPositive growthBounds constantPositive powerAtLeastTwo powerContracts
      secondMoment inversePowerMoment (zero_le_one.trans secondAtLeastOne) (zero_le_one.trans inversePowerAtLeastOne)
      secondBound inversePowerBound inverseMoment inverseAtLeastOne inverseBound first second firstMember secondMember

end
end IGSIII34.Percolation

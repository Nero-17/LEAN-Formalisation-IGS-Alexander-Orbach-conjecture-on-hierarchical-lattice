import IGSIII34.Percolation.ResistancePrefixL2
import IGSIII34.Percolation.GenerationRealMoments
import IGSIII.Chemical.SubstitutionPaths.CompactChemicalFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII34.Probability IGSIII.Probability IGSIII.Chemical.Substitution
open scoped _root_.Topology ENNReal

noncomputable def markedNormalizedResistanceFamily (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) :=
  Set.range (fun depth => markedObservableLp rule p positive lessOne fixedPoint depth address true
    (normalizedConfigurationResistance (rule.generation depth).network p))

noncomputable def markedElectricalPrefixApproximationSet (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (coarse : ℕ) (secondMoment : ℝ) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) :=
  factorBall (independentInnovationLaw rule p positive lessOne fixedPoint) 2
      (fun marks => markedGenerationConfiguration rule marks coarse address true)
      (markedGenerationConfiguration_measurable rule coarse address true) (Real.sqrt secondMoment) ∪
    Set.range (fun depth : Fin (coarse + 1) =>
      markedObservableLp rule p positive lessOne fixedPoint depth address true
        (normalizedConfigurationResistance (rule.generation depth).network p))

theorem markedElectricalPrefixApproximationSet_compact (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (coarse : ℕ) (secondMoment : ℝ) :
    IsCompact (markedElectricalPrefixApproximationSet rule p positive lessOne fixedPoint address coarse secondMoment) :=
  (factorBall_compact _ _ _ _ _).union (Set.finite_range _).isCompact

theorem marked_electrical_prefix_conditionalMean_mem_compact (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (coarse fine : ℕ) (secondMoment : ℝ)
    (secondMomentBound : IGSIII34.Probability.finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
        (fun configuration => (normalizedConfigurationResistance (rule.generation (coarse + fine + 1)).network p configuration)^2) ≤ secondMoment) :
    markedObservableLp rule p positive lessOne fixedPoint coarse address true
      (electricalBlockConditionalMean rule p coarse fine) ∈
        markedElectricalPrefixApproximationSet rule p positive lessOne fixedPoint address coarse secondMoment := by
  apply Or.inl
  apply mem_factorBall_of_coe_ae _ _ _ _ _ (electricalBlockConditionalMean rule p coarse fine)
  · exact markedObservableLp_ae rule p positive lessOne fixedPoint coarse address true _
  · exact Real.le_sqrt_of_sq_le
      ((marked_electrical_prefix_conditionalMean_norm_sq_le rule classical p positive lessOne fixedPoint address coarse fine).trans
        secondMomentBound)

theorem markedNormalizedResistanceFamily_compact_closure_of_inverse_moment
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (powerContracts : (rule.edges : ℝ) ^ (1 / power) < deriv rule.network.reliability p)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, IGSIII34.Probability.finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)^2) ≤ secondMoment)
    (inverseMomentBound : ∀ depth,
      IGSIII34.Probability.finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    IsCompact (closure (markedNormalizedResistanceFamily rule p positive lessOne fixedPoint address)) := by
  have derivativePositive : 0 < deriv rule.network.reliability p :=
    zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint classical.scale)
  have ratioNonnegative : 0 ≤ (rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) derivativePositive.le
  have ratioLessOne : (rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p < 1 :=
    (div_lt_one derivativePositive).mpr powerContracts
  apply compact_closure_of_compact_approximations
    (markedNormalizedResistanceFamily rule p positive lessOne fixedPoint address)
    (fun coarse => markedElectricalPrefixApproximationSet rule p positive lessOne fixedPoint address coarse secondMoment)
    (fun coarse => Real.sqrt
      ((2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power)) *
        ((rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p) ^ (coarse + 1)))
    (fun coarse => markedElectricalPrefixApproximationSet_compact rule p positive lessOne fixedPoint address coarse secondMoment)
  · have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioLessOne
    have shifted := geometric.mul_const ((rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p)
    have scaled := shifted.const_mul (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power))
    simpa only [Function.comp_def, pow_succ, mul_zero, zero_mul, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp scaled
  · intro coarse _ membership
    obtain ⟨depth, rfl⟩ := membership
    by_cases early : depth ≤ coarse
    · refine ⟨markedObservableLp rule p positive lessOne fixedPoint depth address true
          (normalizedConfigurationResistance (rule.generation depth).network p), Or.inr ?_, ?_⟩
      · exact ⟨⟨depth, by omega⟩, rfl⟩
      · rw [dist_self]
        exact Real.sqrt_nonneg _
    · obtain ⟨fine, rfl⟩ : ∃ fine, depth = coarse + fine + 1 := ⟨depth - coarse - 1, by omega⟩
      refine ⟨markedObservableLp rule p positive lessOne fixedPoint coarse address true
        (electricalBlockConditionalMean rule p coarse fine),
        marked_electrical_prefix_conditionalMean_mem_compact rule classical p positive lessOne fixedPoint address
          coarse fine secondMoment (by
            have parentBound := secondMomentBound (coarse+fine+1)
            rw [positiveNormalizedResistance_observable _ p (fun value => value^2)] at parentBound
            exact parentBound), ?_⟩
      rw [dist_eq_norm]
      exact Real.le_sqrt_of_sq_le (marked_electrical_prefix_residual_variance_geometric rule classical p positive lessOne fixedPoint
        address coarse fine powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
        secondMomentBound (inverseMomentBound fine))

theorem markedNormalizedResistanceFamily_compact_closure
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) :
    IsCompact (closure (markedNormalizedResistanceFamily rule p positive lessOne fixedPoint address)) := by
  obtain ⟨power, powerAtLeastTwo, powerContracts⟩ := exists_inverse_power_contracting (rule.edges : ℝ)
    (deriv rule.network.reliability p)
    (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint classical.scale)
  obtain ⟨secondMoment, secondAtLeastOne, secondBound⟩ :=
    generation_normalizedResistance_uniform_second_moment rule classical p positive lessOne fixedPoint
  obtain ⟨inverseMoment, inverseAtLeastOne, inverseBound⟩ :=
    generation_normalizedResistance_uniform_real_inverse_moment rule classical p positive lessOne fixedPoint power
  exact markedNormalizedResistanceFamily_compact_closure_of_inverse_moment rule classical p positive lessOne fixedPoint address
    powerAtLeastTwo powerContracts secondMoment inverseMoment
    (zero_le_one.trans secondAtLeastOne) (zero_le_one.trans inverseAtLeastOne) secondBound inverseBound

end
end IGSIII34.Percolation

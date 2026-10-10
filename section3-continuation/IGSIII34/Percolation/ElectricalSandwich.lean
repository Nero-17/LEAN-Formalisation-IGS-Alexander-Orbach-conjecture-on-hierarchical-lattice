import IGSIII34.Percolation.ElectricalNormalizedUpper
import IGSIII34.Percolation.ElectricalBoundaryConditioning
import IGSIII34.Percolation.ElectricalGapDominance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

theorem electricalOrbit_conditional_fixed_sandwich (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (valueFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (meanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[⇑value |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
        electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks ∧
      electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks ≤ inverseMean *
        (independentInnovationLaw rule p positive belowOne fixedPoint)[⇑value |
          coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
  have lower := normalized_electrical_boundary_conditional_mean_lower rule p positive belowOne fixedPoint
    growth growthNonnegative value valuePositive inverseIntegrable inverseMean inverseMeanPositive inverseMeanEquality depth
  have upper := normalized_electrical_boundary_conditional_mean_upper rule p positive belowOne fixedPoint
    growth growthNonnegative value valuePositive 1 zero_le_one meanOne depth
  have iterateEquality := Function.iterate_fixed valueFixed (depth+1)
  rw [iterateEquality] at lower upper
  filter_upwards [lower, upper,
    electricalOrbitLp_coe_ae_unit_generation rule p positive belowOne fixedPoint growth growthNonnegative depth]
    with marks lower upper orbitEquality
  rw [orbitEquality]
  exact ⟨by simpa only [one_mul] using upper,
    ((div_le_iff₀ inverseMeanPositive).mp lower).trans_eq (mul_comm _ _)⟩

theorem electricalOrbit_eventually_below_fixed_envelope (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (valueFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (meanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (error : ℝ) (errorPositive : 0 < error) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ᶠ depth : ℕ in atTop,
        electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks ≤ inverseMean * value marks + error := by
  have convergence := coordinatePrefixFiltration_condExp_tendsto
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
    (independentInnovationLaw rule p positive belowOne fixedPoint) (⇑value)
    (Lp.stronglyMeasurable value) ((Lp.memLp value).integrable (by norm_num))
  have sandwiches := ae_all_iff.mpr (electricalOrbit_conditional_fixed_sandwich rule p positive belowOne fixedPoint
    growth growthNonnegative value valuePositive valueFixed meanOne inverseIntegrable inverseMean inverseMeanPositive inverseMeanEquality)
  filter_upwards [convergence, sandwiches] with marks limit bounds
  have upper := (((limit.comp (tendsto_add_atTop_nat 1)).const_mul inverseMean).eventually (gt_mem_nhds (lt_add_of_pos_right (inverseMean * value marks) errorPositive))).mono
    (fun depth comparison => (bounds depth).2.trans comparison.le)
  have shifted : ∀ᶠ depth : ℕ in Filter.map (fun index : ℕ => index+1) atTop,
      electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks ≤ inverseMean * value marks + error := upper
  simpa only [Filter.map_add_atTop_eq_nat] using shifted

end
end IGSIII34.Percolation



import IGSIII34.Percolation.ElectricalSandwich
import IGSIII34.Percolation.ElectricalOrbitInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory

theorem inverse_mean_positive
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Sample → ℝ) (valuePositive : ∀ᵐ sample ∂measure, 0 < value sample)
    (integrable : Integrable (fun sample => (value sample)⁻¹) measure) :
    0 < ∫ sample, (value sample)⁻¹ ∂measure := by
  have positive := valuePositive.mono (fun _ inequality => inv_pos.mpr inequality)
  apply (integral_pos_iff_support_of_nonneg_ae (positive.mono (fun _ inequality => inequality.le)) integrable).mpr
  have supportEquality : Function.support (fun sample => (value sample)⁻¹) =ᵐ[measure] Set.univ := by
    filter_upwards [positive] with sample inequality
    change ((value sample)⁻¹ ≠ 0) = True
    exact propext (iff_true_intro inequality.ne')
  rw [measure_congr supportEquality, measure_univ]
  exact zero_lt_one

end
end IGSIII34.Probability
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

theorem electricalOrbit_eventually_below_arbitrary_fixed_envelope (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (valueFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ᶠ depth : ℕ in atTop,
      electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks ≤
        (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint)*value marks+1 := by
  let inverseMean := ∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint
  have inversePositive := inverse_mean_positive (independentInnovationLaw rule p positive belowOne fixedPoint) value valuePositive inverseIntegrable
  have comparisons (depth : ℕ) : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks ≤ inverseMean*
        (independentInnovationLaw rule p positive belowOne fixedPoint)[⇑value |
          coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
    have lower := normalized_electrical_boundary_conditional_mean_lower rule p positive belowOne fixedPoint
      growth growthNonnegative value valuePositive inverseIntegrable inverseMean inversePositive rfl depth
    rw [Function.iterate_fixed valueFixed] at lower
    filter_upwards [lower, electricalOrbitLp_coe_ae_unit_generation rule p positive belowOne fixedPoint growth growthNonnegative depth]
      with marks lower equality
    rw [equality]
    exact ((div_le_iff₀ inversePositive).mp lower).trans_eq (mul_comm _ _)
  have convergence := coordinatePrefixFiltration_condExp_tendsto
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
    (independentInnovationLaw rule p positive belowOne fixedPoint) (⇑value)
    (Lp.stronglyMeasurable value) ((Lp.memLp value).integrable (by norm_num))
  filter_upwards [convergence, ae_all_iff.mpr comparisons] with marks limit bounds
  have eventual := (((limit.comp (tendsto_add_atTop_nat 1)).const_mul inverseMean).eventually
    (gt_mem_nhds (lt_add_one (inverseMean*value marks)))).mono
      (fun depth inequality => (bounds depth).trans inequality.le)
  have shifted : ∀ᶠ depth : ℕ in Filter.map (fun index : ℕ => index+1) atTop,
      electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks ≤ inverseMean*value marks+1 := eventual
  simpa only [Filter.map_add_atTop_eq_nat] using shifted

end
end IGSIII34.Percolation

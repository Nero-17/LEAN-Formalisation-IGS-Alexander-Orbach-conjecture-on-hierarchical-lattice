import IGSIII34.Percolation.ElectricalBoundaryConditioning
import IGSIII34.Percolation.ElectricalGapIterates
import IGSIII34.Percolation.ElectricalInvariantGap
import IGSIII34.Percolation.ElectricalOmegaPositivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

theorem electricalOrbitLp_coe_ae_unit_generation (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    ⇑(electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1)) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint]
      (fun marks => growth⁻¹^(depth+1)*unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)) := by
  filter_upwards [electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthNonnegative (depth+1),
    independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks equality crossing
  rw [equality, markedGeneration_resistance_eq_iteration rule marks crossing]

theorem invariant_gap_dominates_electrical_cluster (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthAboveOne : 1 < growth)
    (family : Set (Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)))
    (compact : IsCompact family) (familyNonnegative : ∀ value ∈ family, 0 ≤ value)
    (mapsTo : Set.MapsTo (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth) family family)
    (onto : Set.SurjOn (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth) family family)
    (upper : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (upperFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth upper = upper)
    (upperBound : ∀ value ∈ family, value ≤ upper) (absent : upper ∉ family)
    (base : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (baseMembership : base ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    ∃ scale : ℝ, 1 ≤ scale ∧ ∀ value ∈ family, base ≤ scale • (upper - value) := by
  have growthPositive : 0 < growth := zero_lt_one.trans growthAboveOne
  obtain ⟨bound, inverseMoments⟩ := exists_uniform_invariant_electrical_gap_inverse_moments rule classical
    p positive belowOne fixedPoint growth growthAboveOne family compact familyNonnegative mapsTo onto
    upper upperFixed upperBound absent 1
  simp only [pow_one] at inverseMoments
  have scalePositive : 0 < max 1 bound := zero_lt_one.trans_le (le_max_left _ _)
  have shiftedCluster : MapClusterPt base atTop
      (electricalOrbitLp rule p positive belowOne fixedPoint growth ∘ (fun depth => depth+1)) := by
    rw [mapClusterPt_comp, Filter.map_add_atTop_eq_nat]
    exact baseMembership
  obtain ⟨subsequence, increasing, convergence⟩ := shiftedCluster.tendsto_subseq
  obtain ⟨subsubsequence, subIncreasing, pointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp convergence).exists_seq_tendsto_ae
  refine ⟨max 1 bound, le_max_left _ _, fun value membership => ?_⟩
  have conditionalBound (depth : ℕ) :
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks / max 1 bound ≤
          (independentInnovationLaw rule p positive belowOne fixedPoint)[⇑(upper-value) |
            coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks := by
    obtain ⟨preimage, preimageMembership, preimageEquality⟩ := onto.iterate (depth+1) membership
    obtain ⟨gapPositive, inverseIntegrable, inverseBound⟩ := inverseMoments preimage preimageMembership
    have inversePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        0 < ((upper-preimage) marks)⁻¹ := gapPositive.mono (fun _ inequality => inv_pos.mpr inequality)
    have inverseMeanPositive : 0 < ∫ marks, ((upper-preimage) marks)⁻¹
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
      apply (integral_pos_iff_support_of_nonneg_ae (inversePositive.mono (fun _ inequality => inequality.le)) inverseIntegrable).mpr
      have supportEquality : Function.support (fun marks => ((upper-preimage) marks)⁻¹) =ᵐ[
          independentInnovationLaw rule p positive belowOne fixedPoint] Set.univ := by
        filter_upwards [inversePositive] with marks inequality
        change (((upper-preimage) marks)⁻¹ ≠ 0) = True
        exact propext (iff_true_intro inequality.ne')
      rw [measure_congr supportEquality, measure_univ]
      exact zero_lt_one
    have lower := normalized_electrical_boundary_conditional_mean_lower rule p positive belowOne fixedPoint
      growth growthPositive.le (upper-preimage) gapPositive inverseIntegrable _ inverseMeanPositive rfl depth
    have gapComparison := normalizedElectricalTransferLp_iterate_gap_le rule p positive belowOne fixedPoint
      growth growthPositive.le upper preimage (familyNonnegative preimage preimageMembership)
      (upperBound preimage preimageMembership) upperFixed (depth+1)
    rw [preimageEquality] at gapComparison
    have conditionalComparison := condExp_mono (m := coordinatePrefixFiltration
      (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
      ((Lp.memLp ((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] (upper-preimage))).integrable (by norm_num))
      ((Lp.memLp (upper-value)).integrable (by norm_num)) ((Lp.coeFn_le _ _).mpr gapComparison)
    filter_upwards [lower, conditionalComparison,
      electricalOrbitLp_coe_ae_unit_generation rule p positive belowOne fixedPoint growth growthPositive.le depth,
      independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks lower comparison orbitEquality crossing
    rw [orbitEquality]
    have unitPositive : 0 < unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true) := by
      rw [markedGeneration_resistance_eq_iteration rule marks crossing]
      exact electricalIteration_positive rule marks (fun address => crossing address true) (depth+1) []
    exact (div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (inv_nonneg.mpr growthPositive.le) _) unitPositive.le)
      inverseMeanPositive (inverseBound.trans (le_max_right _ _))).trans (lower.trans comparison)
  have conditionalConvergence := coordinatePrefixFiltration_condExp_tendsto
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
    (independentInnovationLaw rule p positive belowOne fixedPoint) (⇑(upper-value))
    (Lp.stronglyMeasurable (upper-value)) ((Lp.memLp (upper-value)).integrable (by norm_num))
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [pointwise, conditionalConvergence, ae_all_iff.mpr conditionalBound,
    Lp.coeFn_smul (max 1 bound) (upper-value)] with marks pointwise conditional allBounds scalarEquality
  rw [scalarEquality, Pi.smul_apply, smul_eq_mul]
  have leftConvergence := pointwise.div_const (max 1 bound)
  have rightConvergence := conditional.comp ((tendsto_add_atTop_nat 1).comp
    (increasing.tendsto_atTop.comp subIncreasing.tendsto_atTop))
  have limitComparison : base marks / max 1 bound ≤ (upper-value) marks :=
    le_of_tendsto_of_tendsto leftConvergence rightConvergence
      (Filter.Eventually.of_forall (fun index => allBounds (subsequence (subsubsequence index))))
  exact (div_le_iff₀ scalePositive).mp limitComparison |>.trans_eq (mul_comm _ _)

end
end IGSIII34.Percolation



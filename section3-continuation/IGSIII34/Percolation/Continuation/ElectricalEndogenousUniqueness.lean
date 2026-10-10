import IGSIII34.Percolation.Continuation.ElectricalReciprocal
import IGSIII34.Percolation.ElectricalAmplitudes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (constantPositive : 0 < constant) (growthAboveOne : 1 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint
local notation "W" => electricalOrbitLp rule p positive belowOne fixedPoint growth
local notation "T" => normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth

include classical constantPositive growthAboveOne growthBounds in
theorem electrical_fixed_cluster_eq_mean_smul_arbitrary_fixed
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (value : Lp ℝ 2 μ) (valueFixed : T value = value)
    (valuePositive : ∀ᵐ marks ∂μ, 0 < value marks)
    (meanOne : (∫ marks, value marks ∂μ) = 1)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) μ) :
    endpoint = (∫ marks, endpoint marks ∂μ) • value := by
  have growthPositive := zero_lt_one.trans growthAboveOne
  let inverseMean := ∫ marks, (value marks)⁻¹ ∂μ
  have inversePositive := inverse_mean_positive μ value valuePositive inverseIntegrable
  have orbitLimit := electricalOrbitLp_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
    growthPositive growthBounds endpoint endpointFixed membership
  have uniqueMember (member : Lp ℝ 2 μ) (memberMembership : member ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
      member = endpoint := by
    obtain ⟨subsequence, increasing, limit⟩ := memberMembership.tendsto_subseq
    exact tendsto_nhds_unique limit (orbitLimit.comp increasing.tendsto_atTop)
  have endpointLimit := electricalOrbitLp_tendsto_ae_fixed_cluster rule classical p positive belowOne fixedPoint constant growth
    constantPositive growthPositive growthBounds endpoint endpointFixed membership
  have valueLimit := coordinatePrefixFiltration_condExp_tendsto
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) μ value
    (Lp.stronglyMeasurable value) ((Lp.memLp value).integrable (by norm_num))
  have sandwiches := ae_all_iff.mpr (electricalOrbit_conditional_fixed_sandwich rule p positive belowOne fixedPoint growth growthPositive.le
    value valuePositive valueFixed meanOne inverseIntegrable inverseMean inversePositive rfl)
  have lowerAe : ∀ᵐ marks ∂μ, value marks ≤ endpoint marks := by
    filter_upwards [endpointLimit, valueLimit, sandwiches] with marks endpointLimit valueLimit bounds
    exact le_of_tendsto_of_tendsto (valueLimit.comp (tendsto_add_atTop_nat 1))
      (endpointLimit.comp (tendsto_add_atTop_nat 1)) (Eventually.of_forall (fun depth => (bounds depth).1))
  have upperAe : ∀ᵐ marks ∂μ, endpoint marks ≤ inverseMean*value marks := by
    filter_upwards [endpointLimit, valueLimit, sandwiches] with marks endpointLimit valueLimit bounds
    exact le_of_tendsto_of_tendsto (endpointLimit.comp (tendsto_add_atTop_nat 1))
      ((valueLimit.comp (tendsto_add_atTop_nat 1)).const_mul inverseMean)
      (Eventually.of_forall (fun depth => (bounds depth).2))
  have lower : value ≤ endpoint := (Lp.coeFn_le _ _).mp lowerAe
  have upper : endpoint ≤ inverseMean • value := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [upperAe, Lp.coeFn_smul inverseMean value] with marks inequality equality
    simpa only [equality, Pi.smul_apply, smul_eq_mul] using inequality
  obtain ⟨scalar, scalarPositive, scalarMember, _, _⟩ := electricalOmega_has_fixed_ray_upper_endpoint rule classical
    p positive belowOne fixedPoint constant growth growthAboveOne growthBounds value valueFixed valuePositive
    1 inverseMean zero_lt_one
    (fun member memberMembership => by rw [uniqueMember member memberMembership, one_smul]; exact lower)
    (fun member memberMembership => by rw [uniqueMember member memberMembership]; exact upper)
  have equality := uniqueMember (scalar • value) scalarMember
  have scalarEquality : scalar = ∫ marks, endpoint marks ∂μ := by
    rw [← equality, integral_congr_ae (Lp.coeFn_smul scalar value)]
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, meanOne, mul_one]
  exact equality.symm.trans (by rw [scalarEquality])

include classical constantPositive growthAboveOne growthBounds in
theorem electrical_mean_one_endogenous_fixed_unique
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (first second : Lp ℝ 2 μ)
    (firstFixed : T first = first) (secondFixed : T second = second)
    (firstPositive : ∀ᵐ marks ∂μ, 0 < first marks) (secondPositive : ∀ᵐ marks ∂μ, 0 < second marks)
    (firstMeanOne : (∫ marks, first marks ∂μ) = 1) (secondMeanOne : (∫ marks, second marks ∂μ) = 1)
    (firstInverseIntegrable : Integrable (fun marks => (first marks)⁻¹) μ)
    (secondInverseIntegrable : Integrable (fun marks => (second marks)⁻¹) μ) : first = second := by
  have firstEquality := electrical_fixed_cluster_eq_mean_smul_arbitrary_fixed rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthAboveOne growthBounds endpoint endpointFixed membership first firstFixed firstPositive
    firstMeanOne firstInverseIntegrable
  have secondEquality := electrical_fixed_cluster_eq_mean_smul_arbitrary_fixed rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthAboveOne growthBounds endpoint endpointFixed membership second secondFixed secondPositive
    secondMeanOne secondInverseIntegrable
  have endpointMeanPositive := lp2_integral_positive μ endpoint
    (electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth (zero_lt_one.trans growthAboveOne)
      (fun depth => (growthBounds depth).1) endpoint membership)
  exact (smul_right_injective _ endpointMeanPositive.ne') (firstEquality.symm.trans secondEquality)

end
end IGSIII34.Percolation

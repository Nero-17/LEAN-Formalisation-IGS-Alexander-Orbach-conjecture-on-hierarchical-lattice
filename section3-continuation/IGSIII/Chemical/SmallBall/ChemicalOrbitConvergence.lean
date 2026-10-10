import IGSIII.Chemical.SmallBall.EndpointExponentialBlock
import IGSIII.Chemical.SmallBall.FixedBlockConvergence
import IGSIII.Chemical.SmallBall.ChemicalOmegaEndpoint
import IGSIII.Chemical.ChemicalOmegaMean
import IGSIII.Chemical.EndogenousExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Filter
open scoped ENNReal Topology

noncomputable section

theorem chemicalOrbit_tendsto_ae_of_omega_fixed_ray_endpoint
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (fixedIdentity : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth fixed = fixed)
    (fixedPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < fixed marks)
    (amplitude : ℝ) (amplitudePositive : 0 < amplitude)
    (endpoint : amplitude • fixed ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      Tendsto (fun depth => chemicalOrbit rule p positive lessOne fixedPoint growth depth marks) atTop
        (𝓝 ((amplitude • fixed) marks)) := by
  have countPositive : (0 : ℝ) < (((rule.edges + 3) ^ 4 : ℕ) : ℝ) := by positivity
  have ratioPositive : 0 < (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ := inv_pos.mpr (by positivity)
  have geometricIdentity : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) *
      (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ = 1 / 2 := by field_simp
  have geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) *
      (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ < 1 := by rw [geometricIdentity]; norm_num
  have sandwiches : ∀ index : ℕ, ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∀ᶠ depth : ℕ in atTop,
        (amplitude - amplitude / ((index + 2 : ℕ) : ℝ)) * fixed marks ≤
          chemicalOrbit rule p positive lessOne fixedPoint growth depth marks ∧
        chemicalOrbit rule p positive lessOne fixedPoint growth depth marks ≤
          (amplitude + amplitude / ((index + 2 : ℕ) : ℝ)) * fixed marks := by
    intro index
    have errorPositive : 0 < amplitude / ((index + 2 : ℕ) : ℝ) := div_pos amplitudePositive (by positivity)
    have denominatorGreater : (1 : ℝ) < ((index + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 < index + 2 by omega)
    have errorBelow : amplitude / ((index + 2 : ℕ) : ℝ) < amplitude := div_lt_self amplitudePositive denominatorGreater
    obtain ⟨block, parameter, parameterPositive, upperIntegrable, upperBound, lowerIntegrable, lowerBound⟩ :=
      exists_chemicalOrbit_signed_exponential_block_of_omega_endpoint rule classical p positive lessOne fixedPoint
        constant growth constantPositive growthPositive meanBounds fixed fixedPositive amplitude amplitudePositive endpoint
        errorPositive errorBelow ratioPositive
    exact chemicalOrbit_eventually_between_of_fixed_block rule classical p positive lessOne fixedPoint
      growth growthPositive fixed fixedIdentity
      (amplitude - amplitude / ((index + 2 : ℕ) : ℝ)) (amplitude + amplitude / ((index + 2 : ℕ) : ℝ))
      (sub_nonneg.mpr errorBelow.le) block parameterPositive ratioPositive.le geometricBelowOne
      upperIntegrable upperBound lowerIntegrable lowerBound
  have convergence := ae_tendsto_of_countable_eventual_sandwich
    (independentInnovationLaw rule p positive lessOne fixedPoint)
    (fun depth marks => chemicalOrbit rule p positive lessOne fixedPoint growth depth marks) fixed amplitude sandwiches
  filter_upwards [convergence, Lp.coeFn_smul amplitude fixed] with marks limit equality
  simpa only [equality, Pi.smul_apply, smul_eq_mul] using limit

theorem chemicalOmega_fixed_ray_scalar_atLeastOne
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth)
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (meanOne : (∫ marks, fixed marks ∂independentInnovationLaw rule p positive lessOne fixedPoint) = 1)
    (amplitude : ℝ)
    (endpoint : amplitude • fixed ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
    1 ≤ amplitude := by
  have meanLower := chemicalOmega_mean_atLeastOne rule classical p positive lessOne fixedPoint growth growthPositive
    lowerMeans (amplitude • fixed) endpoint
  have meanEquality : (∫ marks, (amplitude • fixed) marks ∂independentInnovationLaw rule p positive lessOne fixedPoint) = amplitude := by
    rw [integral_congr_ae (Lp.coeFn_smul amplitude fixed)]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, meanOne, mul_one]
  rwa [meanEquality] at meanLower

theorem exists_actual_chemical_orbit_convergence
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      ∃ fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint),
        normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth fixed = fixed ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < fixed marks) ∧
        (∫ marks, fixed marks ∂independentInnovationLaw rule p positive lessOne fixedPoint) = 1 ∧
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
          (∀ member ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
            lower • fixed ≤ member ∧ member ≤ upper • fixed) ∧
          ∃ amplitude : ℝ, 1 ≤ amplitude ∧
            amplitude • fixed ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth ∧
            (∀ member ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth, member ≤ amplitude • fixed) ∧
            (∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
              Tendsto (fun depth => chemicalOrbit rule p positive lessOne fixedPoint growth depth marks) atTop
                (𝓝 ((amplitude • fixed) marks))) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, stationary, lower, upper, lowerPositive, upperPositive, comparison⟩ :=
      exists_actual_positive_endogenous_chemical_field rule classical p positive lessOne fixedPoint
  have growthPositive : 0 < growth :=
    lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt classical.scale) growthLower
  obtain ⟨amplitude, amplitudePositive, endpoint, dominates, least⟩ :=
    chemicalOmega_has_fixed_ray_upper_endpoint rule classical p positive lessOne fixedPoint
      constant growth growthPositive meanBounds fixed fixedIdentity fixedPositive lower upper lowerPositive
      (fun member membership => (comparison member membership).1)
      (fun member membership => (comparison member membership).2)
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, lower, upper, lowerPositive, upperPositive, comparison,
    amplitude, ?_, endpoint, dominates, ?_⟩
  · exact chemicalOmega_fixed_ray_scalar_atLeastOne rule classical p positive lessOne fixedPoint
      growth growthPositive (fun depth => (meanBounds depth).1) fixed meanOne amplitude endpoint
  · exact chemicalOrbit_tendsto_ae_of_omega_fixed_ray_endpoint rule classical p positive lessOne fixedPoint
      constant growth constantPositive growthPositive meanBounds fixed fixedIdentity fixedPositive
      amplitude amplitudePositive endpoint
theorem chemicalOmega_member_eq_of_orbit_ae_tendsto
    (rule : Rule) (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (limit : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (convergence : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      Tendsto (fun depth => chemicalOrbit rule p positive lessOne fixedPoint growth depth marks) atTop (𝓝 (limit marks)))
    (point : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (membership : point ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) : point = limit := by
  obtain ⟨subsequence, increasing, subsequenceConvergence⟩ := membership.tendsto_subseq
  obtain ⟨subsubsequence, subIncreasing, pointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp subsequenceConvergence).exists_seq_tendsto_ae
  apply Lp.ext
  filter_upwards [pointwise, convergence] with marks clusterLimit orbitLimit
  exact tendsto_nhds_unique clusterLimit
    (orbitLimit.comp (increasing.tendsto_atTop.comp subIncreasing.tendsto_atTop))

theorem chemicalOmega_eq_singleton_of_fixed_ray_endpoint
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (fixedIdentity : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth fixed = fixed)
    (fixedPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < fixed marks)
    (amplitude : ℝ) (amplitudePositive : 0 < amplitude)
    (endpoint : amplitude • fixed ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
    chemicalOmegaSet rule p positive lessOne fixedPoint growth = {amplitude • fixed} := by
  apply Set.ext
  intro point
  constructor
  · intro membership
    exact Set.mem_singleton_iff.mpr (chemicalOmega_member_eq_of_orbit_ae_tendsto rule p positive lessOne fixedPoint growth
      (amplitude • fixed) (chemicalOrbit_tendsto_ae_of_omega_fixed_ray_endpoint rule classical p positive lessOne fixedPoint
        constant growth constantPositive growthPositive meanBounds fixed fixedIdentity fixedPositive amplitude amplitudePositive endpoint)
      point membership)
  · intro membership
    exact (Set.mem_singleton_iff.mp membership) ▸ endpoint
end
end IGSIII.Chemical.SmallBall
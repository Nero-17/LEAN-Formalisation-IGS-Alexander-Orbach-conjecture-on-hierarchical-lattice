import IGSIII.Geometry.BoxDimensionDefinition
import IGSIII.Geometry.ActualCriticalMesh

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Matrix MeasureTheory Filter
open scoped Topology NNReal ENNReal

theorem exists_admissible_box_mesh (population growth exponent : ℝ)
    (population_large : 1 < population) (growth_large : 1 < growth)
    (exponent_large : Real.log population / Real.log growth < exponent) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ 1 < growth * eta ∧ population * eta ^ exponent = 1 := by
  have population_positive := zero_lt_one.trans population_large
  have growth_positive := zero_lt_one.trans growth_large
  have log_population_positive := Real.log_pos population_large
  have log_growth_positive := Real.log_pos growth_large
  have exponent_positive := (div_pos log_population_positive log_growth_positive).trans exponent_large
  refine ⟨Real.exp (-Real.log population / exponent), Real.exp_pos _, ?_, ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos log_population_positive) exponent_positive
  · rw [← Real.exp_log growth_positive, ← Real.exp_add, Real.one_lt_exp_iff]
    have inequality := (div_lt_iff₀ log_growth_positive).mp exponent_large
    have quotient := (div_lt_iff₀ exponent_positive).mpr (by simpa only [mul_comm] using inequality)
    rw [neg_div]
    linarith
  · rw [← Real.exp_mul, div_mul_cancel₀ _ exponent_positive.ne', ← Real.exp_log population_positive,
      ← Real.exp_add, Real.log_exp, add_neg_cancel, Real.exp_zero]

variable (rule : Rule) (classical : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scale_positive : 0 < scale)
variable (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < limit_length depth edge)
variable (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge)))

theorem actualChemicalSpace_upperBoxDimension_le
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_positive : 0 < eta) (eta_lt_one : eta < 1)
    (coefficient_positive : 0 < coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (population population_coefficient exponent : ℝ) (population_positive : 0 < population)
    (population_coefficient_positive : 0 < population_coefficient)
    (exponent_nonnegative : 0 ≤ exponent) (subcritical : population * eta ^ exponent ≤ 1)
    (population_bound : ∀ depth,
      (Nat.card (RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) : ℝ) ≤
        population_coefficient * population ^ depth) :
    upperBoxDimension (ActualChemicalSpace rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence) ≤ (exponent : EReal) := by
  apply upperBoxDimension_le_of_covering_power_bound exponent
    (population_coefficient * population ^ (start + 1) * (coefficient * eta ^ (start + 1)) ^ exponent)
    (coefficient * eta ^ (start + 1)) (by positivity)
  exact actualChemicalSpace_covering_power_bound rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence marks configuration_identity eta coefficient start eta_positive eta_lt_one
    coefficient_positive radius_bound population population_coefficient exponent population_positive population_coefficient_positive
    exponent_nonnegative subcritical population_bound

/-- For the actual critical law, every admissible geometric mesh gives its
covering exponent on the constructed chemical completion. The population and
component-radius bounds are both proved from the same actual mark sample. -/
theorem exists_actual_critical_upper_box_exponents (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive_probability : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ (growth : ℝ) (growth_positive : 0 < growth),
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∀ eta : ℝ, 0 < eta → eta < 1 → 1 < growth * eta →
        ∀ exponent : ℝ, 0 ≤ exponent →
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * eta ^ exponent ≤ 1 →
        ∀ᵐ marks ∂independentInnovationLaw rule p positive_probability below_one fixed_point,
          ∀ (coherent : configurationSequenceCoherent rule
              (fun depth => markedGenerationConfiguration rule marks depth [] true))
            (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
            (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
            (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true →
              0 < limit_length depth edge)
            (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
              (((rule.generation fine).network.openGraph
                (generationBlockCells rule coarse fine
                  (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
                  (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
                growth ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge))),
          upperBoxDimension (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
            limit_length nonnegative positive child_convergence) ≤ (exponent : EReal) := by
  obtain ⟨growth, growth_lower, growth_upper, radius_bounds⟩ :=
    exists_actual_critical_uniform_component_mesh rule classicalRule p positive_probability below_one fixed_point
  have growth_positive : 0 < growth :=
    (show (0 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale).trans_le growth_lower
  have population_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive_probability below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p positive_probability below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨growth, growth_positive, growth_lower, growth_upper, ?_⟩
  intro eta eta_positive eta_lt_one product_large exponent exponent_nonnegative subcritical
  filter_upwards [radius_bounds eta eta_positive eta_lt_one product_large,
    actual_retained_skeleton_population_bound classicalRule p positive_probability below_one fixed_point] with marks radius_bounds population_bounds
  obtain ⟨start, radius_bounds⟩ := radius_bounds
  obtain ⟨population_coefficient, coefficient_positive, population_bound⟩ := population_bounds []
  intro coherent limit_length nonnegative positive child_convergence
  exact actualChemicalSpace_upperBoxDimension_le rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
    limit_length nonnegative positive child_convergence marks (fun _ => rfl) eta
    ((rule.edges + 1 : ℝ) / (1 - eta)) start eta_positive eta_lt_one
    (div_pos (by positivity) (sub_pos.mpr eta_lt_one)) radius_bounds
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    population_coefficient exponent population_positive coefficient_positive exponent_nonnegative subcritical population_bound

/-- The upper box dimension of the actual critical chemical completion is at
most log rho / log lambda. Only the actual convergent block lengths used to
construct that completion remain as geometric inputs. -/
theorem exists_actual_critical_upper_box_dimension (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive_probability : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ (growth : ℝ) (growth_positive : 0 < growth),
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive_probability below_one fixed_point,
        ∀ (coherent : configurationSequenceCoherent rule
            (fun depth => markedGenerationConfiguration rule marks depth [] true))
          (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
          (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
          (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true →
            0 < limit_length depth edge)
          (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
            (((rule.generation fine).network.openGraph
              (generationBlockCells rule coarse fine
                (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
                (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
              growth ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge))),
        upperBoxDimension (ActualChemicalSpace rule classicalRule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
          limit_length nonnegative positive child_convergence) ≤
            ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
              Real.log growth : ℝ) : EReal) := by
  obtain ⟨growth, growth_positive, growth_lower, growth_upper, exponents⟩ :=
    exists_actual_critical_upper_box_exponents rule classicalRule p positive_probability below_one fixed_point
  have growth_large : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growth_lower
  have population_large : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive_probability below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p positive_probability below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have dimension_positive : 0 < Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
      Real.log growth := div_pos (Real.log_pos population_large) (Real.log_pos growth_large)
  have mesh_exists (depth : ℕ) := exists_admissible_box_mesh
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) growth
    (Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth +
      1 / ((depth : ℝ) + 1)) population_large growth_large (lt_add_of_pos_right _ (by positivity))
  choose eta eta_positive eta_lt_one eta_growth eta_identity using mesh_exists
  have all_bounds := ae_all_iff.mpr (fun depth : ℕ => exponents (eta depth)
    (eta_positive depth) (eta_lt_one depth) (eta_growth depth)
    (Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth +
      1 / ((depth : ℝ) + 1)) (by positivity) (eta_identity depth).le)
  refine ⟨growth, growth_positive, growth_lower, growth_upper, ?_⟩
  filter_upwards [all_bounds] with marks all_bounds
  intro coherent limit_length nonnegative positive child_convergence
  have convergence : Tendsto (fun depth : ℕ =>
      ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth +
        1 / ((depth : ℝ) + 1) : ℝ) : EReal)) atTop
        (𝓝 ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto' convergence (fun depth => all_bounds depth coherent limit_length nonnegative positive child_convergence)

end
end IGSIII.Geometry

import IGSIII.Geometry.BoxDimensionActualUpper
import IGSIII.Geometry.CriticalChemicalLengths

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open IGSIII.Chemical.SmallBall Matrix MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-- The actual covering theorem uses the very same chemical growth as the
scalar limit, identified through the proved mean bounds. -/
theorem actual_critical_upper_box_dimension_of_mean_bounds
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive_probability : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (constant growth : ℝ) (growth_large : 1 < growth)
    (mean_bounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
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
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth (zero_lt_one.trans growth_large)
        limit_length nonnegative positive child_convergence) ≤
          ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
            Real.log growth : ℝ) : EReal) := by
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
  have all_meshes := ae_all_iff.mpr (fun depth : ℕ =>
    actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive_probability below_one fixed_point
      constant growth (zero_lt_one.trans growth_large) mean_bounds (eta depth) (eta_positive depth)
        (eta_lt_one depth) (eta_growth depth))
  filter_upwards [all_meshes,
    actual_retained_skeleton_population_bound classicalRule p positive_probability below_one fixed_point] with marks meshes population_bounds
  obtain ⟨population_coefficient, coefficient_positive, population_bound⟩ := population_bounds []
  intro coherent limit_length nonnegative positive child_convergence
  have exponent_bound (depth : ℕ) :
      upperBoxDimension (ActualChemicalSpace rule classicalRule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth (zero_lt_one.trans growth_large)
        limit_length nonnegative positive child_convergence) ≤
          ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth +
            1 / ((depth : ℝ) + 1) : ℝ) : EReal) := by
    obtain ⟨start, radius_bounds⟩ := meshes depth
    exact actualChemicalSpace_upperBoxDimension_le rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth (zero_lt_one.trans growth_large)
      limit_length nonnegative positive child_convergence marks (fun _ => rfl) (eta depth)
      ((rule.edges + 1 : ℝ) / (1 - eta depth)) start (eta_positive depth) (eta_lt_one depth)
      (div_pos (by positivity) (sub_pos.mpr (eta_lt_one depth))) radius_bounds
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
      population_coefficient
      (Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth +
        1 / ((depth : ℝ) + 1)) (zero_lt_one.trans population_large) coefficient_positive
      (by positivity) (eta_identity depth).le population_bound
  have convergence : Tendsto (fun depth : ℕ =>
      ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth +
        1 / ((depth : ℝ) + 1) : ℝ) : EReal)) atTop
        (𝓝 ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto' convergence exponent_bound

end
end IGSIII.Geometry

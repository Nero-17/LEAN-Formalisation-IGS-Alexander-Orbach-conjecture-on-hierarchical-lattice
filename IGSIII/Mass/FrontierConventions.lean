import IGSIII.Mass.CompatibleCylinders

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Mass

open Filter MeasureTheory
open scoped Topology

/-- Any bounded change in the assignment of finitely many planting vertices
vanishes after the genuine mass normalization. -/
theorem bounded_frontier_error_tendsto_zero (error : ℕ → ℝ) (radius bound : ℝ)
    (radius_gt_one : 1 < radius) (bounded : ∀ n, |error n| ≤ bound) :
    Tendsto (fun n => error n / radius ^ n) atTop (𝓝 0) := by
  have radius_positive := zero_lt_one.trans radius_gt_one
  have vanishing : Tendsto (fun n : ℕ => bound / radius ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (show |radius⁻¹| < 1 by
          rw [abs_of_pos (inv_pos.mpr radius_positive)]
          exact inv_lt_one_of_one_lt₀ radius_gt_one)).const_mul bound
  apply squeeze_zero_norm _ vanishing
  intro n
  simpa only [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos radius_positive n)] using
    div_le_div_of_nonneg_right (bounded n) (pow_pos radius_positive n).le

theorem ratio_limit_frontier_invariant (numerator denominator numerator_error denominator_error : ℕ → ℝ)
    (radius numerator_limit denominator_limit bound : ℝ)
    (radius_gt_one : 1 < radius) (denominator_nonzero : denominator_limit ≠ 0)
    (numerator_convergence : Tendsto (fun n => numerator n / radius ^ n) atTop (𝓝 numerator_limit))
    (denominator_convergence : Tendsto (fun n => denominator n / radius ^ n) atTop (𝓝 denominator_limit))
    (numerator_bounded : ∀ n, |numerator_error n| ≤ bound)
    (denominator_bounded : ∀ n, |denominator_error n| ≤ bound) :
    Tendsto (fun n => (numerator n + numerator_error n) / (denominator n + denominator_error n))
      atTop (𝓝 (numerator_limit / denominator_limit)) := by
  have numerator_total := numerator_convergence.add
    (bounded_frontier_error_tendsto_zero numerator_error radius bound radius_gt_one numerator_bounded)
  have denominator_total := denominator_convergence.add
    (bounded_frontier_error_tendsto_zero denominator_error radius bound radius_gt_one denominator_bounded)
  simp only [add_zero] at numerator_total denominator_total
  have ratio := numerator_total.div denominator_total denominator_nonzero
  convert ratio using 1
  ext n
  simp only [Pi.add_apply, Pi.div_apply, ← add_div]
  exact (div_div_div_cancel_right₀ (pow_ne_zero n (zero_lt_one.trans radius_gt_one).ne')
    (numerator n + numerator_error n) (denominator n + denominator_error n)).symm

end IGSIII.Mass

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- The actual cylinder ratios are unchanged by every bounded frontier
allocation, in the numerator and in the global root count simultaneously. -/
theorem retained_cylinder_frontier_conventions {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ cylinder : List (Fin rule.edges) → OrientedState →
        (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
        cylinder [] .connected marks = 1 ∧
        ∀ address parent,
          0 ≤ cylinder address parent marks ∧
          cylinder address parent marks =
            ∑ edge, cylinder (address ++ [edge])
              (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
                (marks (address, parent.massOpened)) edge) marks ∧
          (parent = .connected → 0 < cylinder address parent marks) ∧
          (parent = .both → cylinder address .both marks =
            cylinder address .sourceOnly marks + cylinder address .targetOnly marks) ∧
          ∀ (numerator_error denominator_error : ℕ → ℝ) (bound : ℝ),
            (∀ n, |numerator_error n| ≤ bound) → (∀ n, |denominator_error n| ≤ bound) →
            Tendsto (fun n =>
              (markedOrientedVertexMass rule marks n address parent + numerator_error n) /
                (markedOrientedVertexMass rule marks (n + address.length) [] .connected + denominator_error n))
              atTop (𝓝 (cylinder address parent marks)) := by
  obtain ⟨cylinder, cylinder_properties⟩ := compatible_retained_component_cylinder_limits classicalRule p positive below_one fixed_point
  obtain ⟨limit, _, _, convergence⟩ := marked_oriented_vertex_limits classicalRule p positive below_one fixed_point
  have radius_gt_one : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have radius_positive := zero_lt_one.trans radius_gt_one
  refine ⟨cylinder, ?_⟩
  filter_upwards [cylinder_properties, convergence] with marks cylinder_properties convergence
  refine ⟨cylinder_properties.1, ?_⟩
  intro address parent
  obtain ⟨nonnegative, original_ratio, compatible, connected_positive, joint_split⟩ := cylinder_properties.2 address parent
  refine ⟨nonnegative, compatible, connected_positive, joint_split, ?_⟩
  intro numerator_error denominator_error bound numerator_bounded denominator_bounded
  have denominator_positive := mul_pos (pow_pos radius_positive address.length) ((convergence [] .connected).2.2 rfl)
  have shifted_root := ((convergence [] .connected).2.1.comp (tendsto_add_atTop_nat address.length)).const_mul
    (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length)
  have denominator_convergence : Tendsto
      (fun n => markedOrientedVertexMass rule marks (n + address.length) [] .connected /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length *
        limit [] .connected marks)) := by
    convert shifted_root using 1
    ext n
    simp only [Function.comp_apply, pow_add]
    field_simp
  have unperturbed := (convergence address parent).2.1.div denominator_convergence denominator_positive.ne'
  have normalization : Tendsto
      (fun n => markedOrientedVertexMass rule marks n address parent /
        markedOrientedVertexMass rule marks (n + address.length) [] .connected)
      atTop (𝓝 (limit address parent marks /
        (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length *
          limit [] .connected marks))) := by
    convert unperturbed using 1
    ext n
    simp only [Pi.div_apply]
    exact (div_div_div_cancel_right₀ (pow_ne_zero n radius_positive.ne') _ _).symm
  rw [← tendsto_nhds_unique normalization original_ratio]
  exact IGSIII.Mass.ratio_limit_frontier_invariant _ _ numerator_error denominator_error _ _ _ bound
    radius_gt_one denominator_positive.ne' (convergence address parent).2.1 denominator_convergence
      numerator_bounded denominator_bounded

end IGSIII.Chemical.Substitution

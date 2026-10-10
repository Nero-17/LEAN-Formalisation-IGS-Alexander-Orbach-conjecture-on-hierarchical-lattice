import IGSIII.Mass.CylinderMassLimits

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology BigOperators

/-- Passing the actual birth-cell decomposition to the full generation limit
gives a compatible mass field. The bounded top-level reward vanishes. -/
theorem marked_mass_limit_compatible (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (radius : ℝ) (radius_gt_one : 1 < radius)
    (limit : List (Fin rule.edges) → OrientedState → ℝ)
    (convergence : ∀ address parent,
      Tendsto (fun n => markedOrientedVertexMass rule marks n address parent / radius ^ n)
        atTop (𝓝 (limit address parent))) :
    ∀ address parent, radius * limit address parent =
      ∑ edge, limit (address ++ [edge])
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (address, parent.massOpened)) edge) := by
  intro address parent
  have radius_positive := zero_lt_one.trans radius_gt_one
  have shifted := ((convergence address parent).comp (tendsto_add_atTop_nat 1)).const_mul radius
  have shifted_value : Tendsto (fun n => markedOrientedVertexMass rule marks (n + 1) address parent / radius ^ n)
      atTop (𝓝 (radius * limit address parent)) := by
    convert shifted using 1
    · ext n
      simp only [Function.comp_apply, pow_succ]
      field_simp
  have reward_zero : Tendsto (fun n =>
      (rule.network.internalStateMass parent (marks (address, parent.massOpened)) : ℝ) / radius ^ n)
      atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (show |radius⁻¹| < 1 by
          rw [abs_of_pos (inv_pos.mpr radius_positive)]
          exact inv_lt_one_of_one_lt₀ radius_gt_one)).const_mul
            (rule.network.internalStateMass parent (marks (address, parent.massOpened)) : ℝ)
  have children_converge := tendsto_finsetSum (Finset.univ : Finset (Fin rule.edges))
    (fun edge _ => convergence (address ++ [edge])
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge))
  have combined := reward_zero.add children_converge
  simp only [zero_add] at combined
  apply tendsto_nhds_unique shifted_value
  apply combined.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only
    rw [markedOrientedVertexMass_substitute rule marks crossing, add_div, Finset.sum_div])

/-- Every actual retained-component cylinder has a limiting normalized vertex
mass. All masks are constructed jointly from the original marks; the limiting
mass field is compatible, connected cylinders are positive, and B splits into
its original two masked sides. -/
theorem compatible_retained_component_cylinder_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ cylinder : List (Fin rule.edges) → OrientedState →
        (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
        cylinder [] .connected marks = 1 ∧
        ∀ address parent,
          0 ≤ cylinder address parent marks ∧
          Tendsto (fun n => markedOrientedVertexMass rule marks n address parent /
            markedOrientedVertexMass rule marks (n + address.length) [] .connected)
            atTop (𝓝 (cylinder address parent marks)) ∧
          cylinder address parent marks =
            ∑ edge, cylinder (address ++ [edge])
              (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
                (marks (address, parent.massOpened)) edge) marks ∧
          (parent = .connected → 0 < cylinder address parent marks) ∧
          (parent = .both → cylinder address .both marks =
            cylinder address .sourceOnly marks + cylinder address .targetOnly marks) := by
  obtain ⟨limit, _, joint_split, convergence⟩ := marked_oriented_vertex_limits classicalRule p positive below_one fixed_point
  have radius_gt_one : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have radius_positive := zero_lt_one.trans radius_gt_one
  refine ⟨fun address parent marks => limit address parent marks /
    (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length *
      limit [] .connected marks), ?_⟩
  filter_upwards [convergence, independentInnovationLaw_crosses rule p positive below_one fixed_point]
    with marks convergence crossing
  have root_positive := (convergence [] .connected).2.2 rfl
  have compatibility := marked_mass_limit_compatible rule marks crossing
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) radius_gt_one
    (fun address parent => limit address parent marks) (fun address parent => (convergence address parent).2.1)
  constructor
  · simp [root_positive.ne']
  intro address parent
  have denominator_positive := mul_pos (pow_pos radius_positive address.length) root_positive
  refine ⟨div_nonneg (convergence address parent).1 denominator_positive.le, ?_, ?_, ?_, ?_⟩
  · have shifted_root := ((convergence [] .connected).2.1.comp (tendsto_add_atTop_nat address.length)).const_mul
      (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length)
    have ratio := (convergence address parent).2.1.div shifted_root denominator_positive.ne'
    convert ratio using 1
    ext n
    simp only [Function.comp_apply, Pi.div_apply]
    by_cases root_zero : markedOrientedVertexMass rule marks (n + address.length) [] .connected = 0
    · simp [root_zero]
    · rw [pow_add]
      field_simp [root_zero, radius_positive.ne']
  · simp only [List.length_append, List.length_singleton]
    rw [← Finset.sum_div, ← compatibility address parent, pow_succ]
    field_simp [radius_positive.ne', root_positive.ne']
  · intro connected
    subst parent
    exact div_pos ((convergence address .connected).2.2 rfl) denominator_positive
  · intro _
    rw [joint_split address marks]
    ring

end IGSIII.Chemical.Substitution

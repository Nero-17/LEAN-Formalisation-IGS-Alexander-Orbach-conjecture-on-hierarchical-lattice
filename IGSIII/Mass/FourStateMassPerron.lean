import IGSIII.Mass.OrientedPrimitivity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- The four-state mass Perron theorem for actual graph histories. Primitivity,
both positive Perron vectors, mean-one positive W, all four coordinate limits,
and the actual birth-reward vertex coefficient are proved in one normalization. -/
theorem Classical.four_state_mass_perron {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ (right left : MassLiveState → ℝ) (coefficient : ℝ)
      (limit : (Π n, rule.ConfigurationHistory n) → ℝ),
      (∀ state child, 0 < (rule.network.orientedMassMatrix p ^ 4) state child) ∧
      spectralRadius ℂ ((rule.network.orientedMassMatrix p).map Complex.ofReal) =
        spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal) ∧
      right .connected = 1 ∧ (∀ state, 0 < right state) ∧ (∀ state, 0 < left state) ∧
      rule.network.orientedMassMatrix p *ᵥ right =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • right ∧
      left ᵥ* rule.network.orientedMassMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • left ∧
      left ⬝ᵥ right = 1 ∧ 0 < coefficient ∧
      coefficient = (left ⬝ᵥ rule.network.orientedMeanVertexReward p) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1) ∧
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) ∧
      (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) = 1 ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true, 0 < limit path) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        ∀ child : MassLiveState,
        Tendsto (fun n => ConfigurationHistory.rootLevelOrientedPopulation rule
          (fun state => if state = child then 1 else 0) n path /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (limit path * left child))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        Tendsto (fun n => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (coefficient * limit path))) := by
  obtain ⟨right, left, coefficient, limit, same_radius, normalized, right_positive, left_nonnegative,
    left_connected_positive, _, right_eigenvector, left_eigenvector, left_normalized,
    coefficient_positive, coefficient_formula, limit_mem, limit_mean, limit_positive,
    coordinate_limit, vertex_limit⟩ := classicalRule.four_state_mass_limit p positive below_one fixed_point
  have primitive := classicalRule.orientedMassMatrix_fourth_power_pos p positive below_one fixed_point
  have radius_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have powered : ∀ n : ℕ, left ᵥ* rule.network.orientedMassMatrix p ^ n =
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n • left := by
    intro n
    induction n with
    | zero => simp
    | succ n induction_hypothesis =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, induction_hypothesis, Matrix.smul_vecMul,
        left_eigenvector, smul_smul, ← pow_succ]
  have left_positive (child : MassLiveState) : 0 < left child := by
    have positive_sum : 0 < (left ᵥ* rule.network.orientedMassMatrix p ^ 4) child := by
      change 0 < ∑ parent, left parent * (rule.network.orientedMassMatrix p ^ 4) parent child
      apply Finset.sum_pos'
      · intro parent _
        exact mul_nonneg (left_nonnegative parent) (primitive parent child).le
      · exact ⟨.connected, Finset.mem_univ _, mul_pos left_connected_positive (primitive .connected child)⟩
    rw [powered] at positive_sum
    exact (mul_pos_iff_of_pos_left (pow_pos radius_positive 4)).mp positive_sum
  exact ⟨right, left, coefficient, limit, primitive, same_radius, normalized, right_positive,
    left_positive, right_eigenvector, left_eigenvector, left_normalized, coefficient_positive,
    coefficient_formula, limit_mem, limit_mean, limit_positive, coordinate_limit, vertex_limit⟩

end Universality.Rule

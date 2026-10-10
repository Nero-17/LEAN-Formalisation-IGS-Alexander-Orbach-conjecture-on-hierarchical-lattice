import Universality.Probability.InhomogeneousMomentComparison
import Universality.Percolation.OffcriticalMomentRecursion
import Universality.Percolation.RenormalisationLimits

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem conditionalVertexMoment_of_weight_comparison (first second factor : ℝ)
    (hfirst : 0 < R.reliability first) (hfirst' : R.reliability first < 1)
    (hsecond : 0 < R.reliability second) (hsecond' : R.reliability second < 1)
    (hpsecond : 0 ≤ second) (hpsecond' : second ≤ 1) (hfactor : 1 ≤ factor)
    (hweight : ∀ opened configuration, R.conditionalCellWeight first opened configuration ≤
      factor * R.conditionalCellWeight second opened configuration) (state : LiveState) (order : ℕ) :
    R.conditionalVertexMoment first state order ≤ factor ^ order * R.conditionalVertexMoment second state order := by
  by_cases horder : order = 0
  · subst order
    simp only [conditionalVertexMoment,
      R.conditionalInternalMoment_zero first hfirst hfirst',
      R.conditionalInternalMoment_zero second hsecond hsecond', pow_zero, one_mul, le_refl]
  have hlinear : R.conditionalVertexMoment first state order ≤ factor * R.conditionalVertexMoment second state order := by
    unfold conditionalVertexMoment conditionalInternalMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro configuration _
    have hb := mul_le_mul_of_nonneg_right (hweight (state == .connected) configuration)
      (pow_nonneg (Nat.cast_nonneg (R.internalSelectedMass true (state == .both) configuration)) order)
    simpa only [mul_assoc] using hb
  exact hlinear.trans (mul_le_mul_of_nonneg_right
    (by simpa using pow_le_pow_right₀ hfactor (show 1 ≤ order by omega))
    (R.conditionalInternalMoment_nonneg second hpsecond hpsecond' _ _ _ _))

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem Classical.generation_moments_parameter_comparison {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hp : 0 < p) (hp' : p < 1)
    (factor : ℕ → ℝ) (depth : ℕ) (hfactor : ∀ n ≤ depth, 1 ≤ factor n)
    (hweight : ∀ n ≤ depth, ∀ opened configuration,
      rule.network.conditionalCellWeight (rule.network.reliability^[n] p) opened configuration ≤
        factor n * rule.network.conditionalCellWeight (rule.network.reliability^[n] critical) opened configuration) :
    ∀ n ≤ depth, ∀ state order,
      (rule.generation n).network.conditionalVertexMoment p state order ≤
        (∏ j ∈ Finset.range (n + 1), factor j) ^ order *
          (rule.generation n).network.conditionalVertexMoment critical state order := by
  apply inhomogeneous_branching_moment_comparison
    (fun n state => rule.network.conditionalCellWeight (rule.network.reliability^[n] p) (state == .connected))
    (fun n state => rule.network.conditionalCellWeight (rule.network.reliability^[n] critical) (state == .connected))
    (fun state configuration => (rule.network.internalSelectedMass true (state == .both) configuration : ℝ))
    rule.network.childState
    (fun n state order => (rule.generation n).network.conditionalVertexMoment p state order)
    (fun n state order => (rule.generation n).network.conditionalVertexMoment critical state order)
    factor depth hfactor
  · intro n _ state configuration
    by_cases hn : n = 0
    · subst n
      exact rule.network.conditionalCellWeight_nonneg hp.le hp'.le _ _
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [← rule.generation_reliability_iterate]
      exact rule.network.conditionalCellWeight_nonneg
        ((rule.generation j).network.reliability_nonneg hp.le hp'.le)
        ((rule.generation j).network.reliability_le_one hp.le hp'.le) _ _
  · intro n _ state configuration
    by_cases hn : n = 0
    · subst n
      exact rule.network.conditionalCellWeight_nonneg hc.le hc'.le _ _
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [← rule.generation_reliability_iterate]
      exact rule.network.conditionalCellWeight_nonneg
        ((rule.generation j).network.reliability_nonneg hc.le hc'.le)
        ((rule.generation j).network.reliability_le_one hc.le hc'.le) _ _
  · intro state configuration
    exact Nat.cast_nonneg _
  · intro n state order
    exact (rule.generation n).network.conditionalInternalMoment_nonneg p hp.le hp'.le _ _ _ _
  · intro n state order
    exact (rule.generation n).network.conditionalInternalMoment_nonneg critical hc.le hc'.le _ _ _ _
  · intro n state
    exact (rule.generation n).network.conditionalInternalMoment_zero p
      (((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr ((h.generation n).connected _))
      ((rule.generation n).network.reliability_lt_one hp hp') _ _ _
  · intro n state
    exact (rule.generation n).network.conditionalInternalMoment_zero critical
      (((rule.generation n).network.reliability_pos_iff_connected hc hc').mpr ((h.generation n).connected _))
      ((rule.generation n).network.reliability_lt_one hc hc') _ _ _
  · intro n hn state configuration
    exact hweight n hn _ _
  · intro state order
    exact rule.network.conditionalVertexMoment_of_weight_comparison p critical (factor 0)
      ((rule.network.reliability_pos_iff_connected hp hp').mpr (h.connected _))
      (rule.network.reliability_lt_one hp hp')
      ((rule.network.reliability_pos_iff_connected hc hc').mpr (h.connected _)) (rule.network.reliability_lt_one hc hc')
      hc.le hc'.le (hfactor 0 (Nat.zero_le _)) (by simpa using hweight 0 (Nat.zero_le _)) state order
  · intro n state order
    simpa only [rule.generation_reliability_iterate] using
      h.generation_conditionalVertexMoment_offcritical p hp hp' n order state
  · intro n state order
    simpa only [rule.generation_reliability_iterate] using
      h.generation_conditionalVertexMoment_offcritical critical hc hc' n order state

end
end Universality.Rule


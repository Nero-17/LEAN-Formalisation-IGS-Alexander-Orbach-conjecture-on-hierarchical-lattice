import Universality.Percolation.SubcriticalSourceMomentBound

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem internalSelectedMass_both_le_source_add_target (configuration : Configuration edges) :
    R.internalSelectedMass true true configuration ≤
      R.internalSelectedMass true false configuration + R.internalSelectedMass false true configuration := by
  unfold internalSelectedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro vertex _
  cases hs : (R.openGraph configuration).reachableDecide R.source vertex.val <;>
    cases ht : (R.openGraph configuration).reachableDecide R.target vertex.val <;>
    simp [selectedActive, hs, ht]

theorem expectedInternalBoundaryMoment_le_sourceMoment
    (symmetry : R.NetworkSymmetry) (hs : symmetry.vertex R.source = R.target)
    (ht : symmetry.vertex R.target = R.source) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (order : ℕ) (horder : 1 ≤ order) :
    R.expectedInternalBoundaryMoment p order ≤ 2 ^ order * R.expectedInternalSourceMoment p order := by
  calc
    _ ≤ ∑ configuration, bernoulliWeight p configuration *
        (2 ^ (order - 1) * ((R.internalSelectedMass true false configuration : ℝ) ^ order +
          (R.internalSelectedMass false true configuration : ℝ) ^ order)) := by
      apply Finset.sum_le_sum
      intro configuration _
      apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _)
        (by exact_mod_cast R.internalSelectedMass_both_le_source_add_target configuration) order).trans
        (add_pow_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) order)
    _ = 2 ^ (order - 1) * (R.expectedInternalSourceMoment p order + R.expectedInternalSourceMoment p order) := by
      simp_rw [mul_left_comm (bernoulliWeight p _) (2 ^ (order - 1))]
      rw [← Finset.mul_sum]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [symmetry.expectedInternalTargetMoment hs ht p order]
      rfl
    _ = _ := by
      have hexp : (2 : ℝ) ^ order = 2 ^ (order - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel horder]
      rw [hexp]
      ring

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem Classical.subcritical_boundary_moment_bound {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hpc : p < critical)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n,
      (rule.generation n).network.expectedInternalBoundaryMoment p order ≤
        bound * (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) := by
  obtain ⟨bound, hbound, hb⟩ := h.subcritical_source_moment_bound critical p hc hc' hfixed hp hpc order horder
  refine ⟨2 ^ order * bound, by positivity, ?_⟩
  intro n
  obtain ⟨symmetry, hs, ht⟩ := (h.generation n).massAdmissible.symmetric
  exact ((rule.generation n).network.expectedInternalBoundaryMoment_le_sourceMoment symmetry hs ht
    hp (hpc.trans hc').le order horder).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb n) (by positivity : (0 : ℝ) ≤ 2 ^ order))

end
end Universality.Rule

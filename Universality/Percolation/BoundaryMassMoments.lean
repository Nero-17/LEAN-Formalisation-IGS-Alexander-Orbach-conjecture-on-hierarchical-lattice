import Universality.Percolation.VertexMomentGrowth
import Universality.Percolation.InternalClusterMassLimit

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def expectedInternalBoundaryMoment (p : ℝ) (order : ℕ) : ℝ :=
  ∑ configuration, bernoulliWeight p configuration *
    (R.internalSelectedMass true true configuration : ℝ) ^ order

theorem expectedInternalBoundaryMoment_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    0 ≤ R.expectedInternalBoundaryMoment p order :=
  Finset.sum_nonneg (fun configuration _ => mul_nonneg (bernoulliWeight_nonneg hp hp' _)
    (pow_nonneg (Nat.cast_nonneg _) _))

theorem expectedInternalBoundaryMoment_disintegrate (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) (order : ℕ) :
    R.expectedInternalBoundaryMoment p order =
      R.reliability p * R.conditionalVertexMoment p .connected order +
        (1 - R.reliability p) * R.conditionalVertexMoment p .both order := by
  change _ = R.reliability p * R.conditionalInternalMoment p true true false order +
    (1 - R.reliability p) * R.conditionalInternalMoment p false true true order
  rw [← R.conditionalInternalMoment_connected]
  unfold expectedInternalBoundaryMoment conditionalInternalMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro configuration _
  unfold conditionalCellWeight
  cases hcross : R.crosses configuration <;>
    simp only [hcross, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;>
    field_simp [hpositive.ne', (sub_pos.mpr hless).ne']
  all_goals ring

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem Classical.internal_boundary_moment_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n,
      (rule.generation n).network.expectedInternalBoundaryMoment p order ≤
        bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order * n) := by
  obtain ⟨bound, hbound, hmoment⟩ := h.internal_vertex_moment_bounds p hp hp' hfixed order
  refine ⟨bound, hbound, ?_⟩
  intro n
  rw [(rule.generation n).network.expectedInternalBoundaryMoment_disintegrate p
    (by rwa [rule.generation_fixed_point p hfixed])
    (by rwa [rule.generation_fixed_point p hfixed]), rule.generation_fixed_point p hfixed]
  have hfirst := mul_le_mul_of_nonneg_left (hmoment n .connected) hp.le
  have hsecond := mul_le_mul_of_nonneg_left (hmoment n .both) (sub_nonneg.mpr hp'.le)
  nlinarith

end
end Universality.Rule

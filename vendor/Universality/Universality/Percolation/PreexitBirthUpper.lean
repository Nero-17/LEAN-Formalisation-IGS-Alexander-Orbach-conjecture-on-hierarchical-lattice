import Universality.Percolation.PreexitMomentBounds
import Universality.Percolation.BirthMomentUpper

namespace Universality.Rule
noncomputable section

theorem Classical.preexit_boundary_moment_bounds {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ order : ℕ, ∃ upper : ℝ, 0 < upper ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) →
          (rule.generation n).network.expectedInternalBoundaryMoment p order ≤
            upper * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * n) := by
  obtain ⟨radius, hradius, hbounds⟩ := h.preexit_moment_bounds critical hc hc' hfixed
  refine ⟨radius, hradius, ?_⟩
  intro order
  obtain ⟨lower, upper, hlower, hupper, hb⟩ := hbounds order
  refine ⟨upper, hupper, ?_⟩
  intro p hp hp' n horbit
  have hpositive := ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr ((h.generation n).connected _)
  have hless := (rule.generation n).network.reliability_lt_one hp hp'
  rw [(rule.generation n).network.expectedInternalBoundaryMoment_disintegrate p hpositive hless]
  have hfirst := mul_le_mul_of_nonneg_left (hb p hp hp' n horbit .connected).2 hpositive.le
  have hsecond := mul_le_mul_of_nonneg_left (hb p hp hp' n horbit .both).2 (sub_nonneg.mpr hless.le)
  nlinarith

theorem Classical.preexit_birth_moment_upper {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ order : ℕ, 1 ≤ order → ∃ upper : ℝ, 0 < upper ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) →
          rule.expectedClusterBirthPower p order (n + 1) ≤
            upper * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * n) := by
  obtain ⟨radius, hradius, hbounds⟩ := h.preexit_boundary_moment_bounds critical hc hc' hfixed
  refine ⟨radius, hradius, ?_⟩
  intro order horder
  obtain ⟨bound, hbound, hb⟩ := hbounds order
  have hvertices : (0 : ℝ) < rule.vertices := by
    have := h.vertices_gt_two
    exact_mod_cast (by omega : 0 < rule.vertices)
  have hedges : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hradius : 1 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1
  refine ⟨((rule.edges : ℝ) + 1) ^ (order - 1) *
    ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * bound), by positivity, ?_⟩
  intro p hp hp' n horbit
  have hupper := rule.network.expectedBirthClusterPower_le_boundary_moment
    (rule.generation n).network hp.le hp'.le order horder
  change rule.expectedClusterBirthPower p order (n + 1) ≤ _ at hupper
  apply hupper.trans
  have hpower := one_le_pow₀ (n := order * n) hradius.le
  have hmoment := mul_le_mul_of_nonneg_left (hb p hp hp' n horbit) hedges.le
  have hvertex := mul_le_mul_of_nonneg_left hpower (pow_nonneg hvertices.le order)
  have hinside : (rule.vertices : ℝ) ^ order +
      (rule.edges : ℝ) * (rule.generation n).network.expectedInternalBoundaryMoment p order ≤
      ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * bound) *
        ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * n) := by
    nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinside
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (rule.edges : ℝ) + 1) _)

end
end Universality.Rule

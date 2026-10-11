import Universality.Percolation.ExitMomentComparison
import Universality.Percolation.PostexitSubcriticalBound
import Universality.Percolation.PostexitSupercriticalBound

namespace Universality.Rule
noncomputable section

theorem Classical.nearcritical_subcritical_birth_pointwise {rule : Rule} (h : rule.Classical)
    (critical lower upper : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hupper : upper < 1)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ tailUpper : ℝ, 0 < tailUpper → tailUpper < critical →
      ∃ constant : ℝ, 0 < constant ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) →
        ∀ exitParameter, rule.network.reliability^[n + 1] p = exitParameter →
          lower ≤ exitParameter → exitParameter ≤ upper → exitParameter ≤ tailUpper →
        ∀ j : ℕ, rule.expectedClusterBirthPower p order ((n + 1) + j + 1) ≤
          constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * (n + 1)) * (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * j) := by
  obtain ⟨radius, hradius, hinitial⟩ := h.exit_moment_initial_bound critical lower upper
    hc hc' hfixed hlower hinterval hupper
  obtain ⟨initial, hinitialOne, hi⟩ := hinitial order
  refine ⟨radius, hradius, ?_⟩
  intro tailUpper htailUpper htailCritical
  obtain ⟨tail, htail, ht⟩ := h.postexit_subcritical_birth_bound critical tailUpper hc hc' hfixed
    htailUpper htailCritical order horder
  have hspectral : 1 ≤ (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1).le
  refine ⟨tail * initial ^ order, mul_pos htail (pow_pos (zero_lt_one.trans_le hinitialOne) _), ?_⟩
  intro p hp hp' n horbit exitParameter hparameter hlow hhigh hexitTail
  have hscale : 1 ≤ initial *
      ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (n + 1) :=
    hinitialOne.trans (le_mul_of_one_le_right (zero_le_one.trans hinitialOne) (one_le_pow₀ hspectral))
  have hb := ht p exitParameter hp hp' (hlower.trans_le hlow) hexitTail (n + 1) hparameter _ hscale
    (hi p hp hp' n horbit exitParameter hparameter hlow hhigh)
  intro j
  refine (hb j).trans_eq ?_
  rw [mul_pow, ← pow_mul, Nat.mul_comm (n + 1) order]
  ring

theorem Classical.nearcritical_supercritical_birth_pointwise {rule : Rule} (h : rule.Classical)
    (critical lower upper : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hupper : upper < 1)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ tailLower : ℝ, critical < tailLower → tailLower < 1 →
      ∃ constant : ℝ, 0 < constant ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) →
        ∀ exitParameter, rule.network.reliability^[n + 1] p = exitParameter →
          lower ≤ exitParameter → exitParameter ≤ upper → tailLower ≤ exitParameter →
        ∀ j : ℕ, rule.expectedClusterBirthPower p order ((n + 1) + j + 1) ≤
          constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * (n + 1)) * (1 / 2 : ℝ) ^ j := by
  obtain ⟨radius, hradius, hinitial⟩ := h.exit_moment_initial_bound critical lower upper
    hc hc' hfixed hlower hinterval hupper
  obtain ⟨initial, hinitialOne, hi⟩ := hinitial (2 * order)
  refine ⟨radius, hradius, ?_⟩
  intro tailLower htailCritical htailLower
  obtain ⟨tail, htail, ht⟩ := h.postexit_supercritical_birth_bound critical tailLower hc hc' hfixed
    htailCritical htailLower order horder
  have hspectral : 1 ≤ (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1).le
  refine ⟨tail * initial ^ order, mul_pos htail (pow_pos (zero_lt_one.trans_le hinitialOne) _), ?_⟩
  intro p hp hp' n horbit exitParameter hparameter hlow hhigh hexitTail
  have hscale : 1 ≤ initial *
      ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (n + 1) :=
    hinitialOne.trans (le_mul_of_one_le_right (zero_le_one.trans hinitialOne) (one_le_pow₀ hspectral))
  have hb := ht p exitParameter hp hp' hexitTail (hhigh.trans_lt hupper) (n + 1) hparameter _ hscale
    (hi p hp hp' n horbit exitParameter hparameter hlow hhigh)
  intro j
  refine (hb j).trans_eq ?_
  rw [mul_pow, ← pow_mul, Nat.mul_comm (n + 1) order]
  ring

end
end Universality.Rule

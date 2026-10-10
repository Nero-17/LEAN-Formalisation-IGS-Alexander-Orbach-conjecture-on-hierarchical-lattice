import Universality.Percolation.ActualExitPointwise
import Universality.Analysis.StoppedSequenceDomination
import Universality.Percolation.DiscountedPostexitPower
import Universality.Percolation.PreexitBirthUpper

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0

/-- A genuine post-exit pointwise estimate yields a geometric majorant
uniform in the percolation parameter and in the birth generation. -/
theorem Classical.birth_series_domination_from_exit_pointwise {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order)
    (decay : ℝ) (hdecay : 0 ≤ decay)
    (allowed : ℝ → Prop) (hallowed : ∀ p, allowed p → 0 < p ∧ p < 1 ∧ p ≠ critical)
    (htail : ∃ neighborhood : ℝ, 0 < neighborhood ∧ neighborhood < critical ∧ neighborhood < 1 - critical ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ neighborhood → ∃ constant : ℝ, 0 < constant ∧
      ∀ p, allowed p → |p - critical| < radius → ∀ j : ℕ,
        rule.expectedClusterBirthPower p order (rule.reliabilityExitTime critical radius p + j + 1) ≤
          constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^
            (order * rule.reliabilityExitTime critical radius p) * decay ^ j) :
    ∃ neighborhood constant : ℝ, 0 < neighborhood ∧ 0 < constant ∧
      ∀ p, allowed p → |p - critical| < neighborhood → ∀ n : ℕ,
        (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1) ≤
          constant * (max
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges)
            (decay / rule.edges)) ^ n := by
  have hm : (0 : ℝ) < rule.edges := by
    have := h.edges_gt_one
    exact_mod_cast (by omega : 0 < rule.edges)
  have hgrowth : 0 ≤ (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    ENNReal.toReal_nonneg
  obtain ⟨tailRadius, htailRadius, htailCritical, htailOne, htailBound⟩ := htail
  obtain ⟨upperRadius, hupperRadius, hupperBounds⟩ := h.preexit_birth_moment_upper critical hc hc' hfixed
  obtain ⟨upper, hupper, hupperBound⟩ := hupperBounds order horder
  let radius : ℝ := min tailRadius upperRadius
  have hradius : 0 < radius := lt_min htailRadius hupperRadius
  have hradiusTail : radius ≤ tailRadius := min_le_left _ _
  have hradiusUpper : radius ≤ upperRadius := min_le_right _ _
  obtain ⟨tail, htailPositive, hpostBound⟩ := htailBound radius hradius hradiusTail
  refine ⟨radius, max (upper / (rule.edges : ℝ) ^ 2) (tail / (rule.edges : ℝ) ^ 2),
    hradius, (div_pos hupper (pow_pos hm _)).trans_le (le_max_left _ _), ?_⟩
  intro p hpAllowed hpNear
  obtain ⟨hp, hp', hpne⟩ := hallowed p hpAllowed
  apply stopped_sequence_geometric_domination _ _ _ _ _ (rule.reliabilityExitTime critical radius p)
    (div_nonneg (pow_nonneg hgrowth _) hm.le) (div_nonneg hdecay hm.le)
    (div_nonneg hupper.le (pow_nonneg hm.le _)) (div_nonneg htailPositive.le (pow_nonneg hm.le _))
  · intro n hn
    have hh := hupperBound p hp hp' n (fun j hj =>
      (h.reliability_exit_before critical radius p hc hc' hfixed
        (hradiusTail.trans_lt htailCritical) (hradiusTail.trans_lt htailOne)
        hp hp' hpne j (hj.trans_lt hn)).trans_le hradiusUpper)
    exact (mul_le_mul_of_nonneg_left hh (pow_nonneg (one_div_nonneg.mpr hm.le) (n + 2))).trans_eq
      (discounted_power_identity _ _ upper hm order n)
  · intro j
    have hh := hpostBound p hpAllowed hpNear j
    exact (mul_le_mul_of_nonneg_left hh
      (pow_nonneg (one_div_nonneg.mpr hm.le) (rule.reliabilityExitTime critical radius p + j + 2))).trans_eq
      (discounted_postexit_power_identity _ _ decay tail hm order (rule.reliabilityExitTime critical radius p) j)

end
end Universality.Rule

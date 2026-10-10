import Universality.Percolation.ActualExitTail
import Universality.Analysis.StoppedSeriesComparison
import Universality.Percolation.BirthSeriesScaling
import Universality.Percolation.PreexitBirthLower
import Universality.Percolation.PreexitBirthUpper

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0

/-- This assembly lemma takes the proved whole-tail interface and combines
it with the actual pre-exit birth estimates. It retains the exact omitted
prefix and final two pre-exit levels. -/
theorem Classical.birth_series_comparison_from_exit_tail {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 1 ≤ order)
    (allowed : ℝ → Prop) (hallowed : ∀ p, allowed p → 0 < p ∧ p < 1 ∧ p ≠ critical)
    (htail : ∃ neighborhood : ℝ, 0 < neighborhood ∧ neighborhood < critical ∧ neighborhood < 1 - critical ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ neighborhood → ∃ constant : ℝ, 0 < constant ∧
      ∀ p, allowed p → |p - critical| < radius →
        Summable (fun j : ℕ => (1 / (rule.edges : ℝ)) ^ j *
          rule.expectedClusterBirthPower p order (rule.reliabilityExitTime critical radius p + j + 1)) ∧
        (∑' j : ℕ, (1 / (rule.edges : ℝ)) ^ j *
          rule.expectedClusterBirthPower p order (rule.reliabilityExitTime critical radius p + j + 1)) ≤
          constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^
            (order * rule.reliabilityExitTime critical radius p)) :
    ∃ radius neighborhood lower upper : ℝ, 0 < radius ∧ radius < critical ∧ radius < 1 - critical ∧
      0 < neighborhood ∧ neighborhood ≤ radius ∧ 0 < lower ∧ 0 < upper ∧
      ∀ p, allowed p → |p - critical| < neighborhood →
        Summable (fun n : ℕ => (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ∧
        lower * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
          (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges) ^ n) ≤
          (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ∧
        (∑' n : ℕ, (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1)) ≤
          upper * (∑ n ∈ Finset.range (rule.reliabilityExitTime critical radius p),
            (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ order / rule.edges) ^ n) := by
  let growth : ℝ := (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal
  have hgrowth : 0 < growth := zero_lt_one.trans
    ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hm : (0 : ℝ) < rule.edges := by have := h.edges_gt_one; exact_mod_cast (by omega : 0 < rule.edges)
  let ratio : ℝ := growth ^ order / rule.edges
  have hratio : 0 < ratio := div_pos (pow_pos hgrowth _) hm
  obtain ⟨tailRadius, htailRadius, htailCritical, htailOne, htailBound⟩ := htail
  obtain ⟨upperRadius, hupperRadius, hupperBounds⟩ := h.preexit_birth_moment_upper critical hc hc' hfixed
  obtain ⟨upper, hupper, hupperBound⟩ := hupperBounds order horder
  obtain ⟨lowerRadius, hlowerRadius, start, hlowerBounds⟩ := h.preexit_birth_moment_eventual_lower critical hc hc' hfixed
  obtain ⟨lower, hlower, hlowerBound⟩ := hlowerBounds order horder
  let radius : ℝ := min tailRadius (min upperRadius lowerRadius) / 2
  have hradius : 0 < radius := div_pos (lt_min htailRadius (lt_min hupperRadius hlowerRadius)) (by norm_num)
  have hradiusMin : radius ≤ min tailRadius (min upperRadius lowerRadius) := by
    dsimp [radius]
    linarith [lt_min htailRadius (lt_min hupperRadius hlowerRadius)]
  have hradiusTail : radius ≤ tailRadius := hradiusMin.trans (min_le_left _ _)
  have hradiusUpper : radius ≤ upperRadius := hradiusMin.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hradiusLower : radius ≤ lowerRadius := hradiusMin.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hradiusCritical : radius < critical := hradiusTail.trans_lt htailCritical
  have hradiusOne : radius < 1 - critical := hradiusTail.trans_lt htailOne
  obtain ⟨tail, htailPositive, hpostBound⟩ := htailBound radius hradius hradiusTail
  obtain ⟨near, hnear, hdepth⟩ := h.reliability_exit_diverges critical radius hc hc' hfixed hradius
    hradiusCritical hradiusOne (start + 2)
  obtain ⟨window, hwindow, hwindowBound⟩ := stopped_series_geometric_lower ratio hratio start
  refine ⟨radius, min near radius, window * (lower / (rule.edges : ℝ) ^ 2),
    upper / (rule.edges : ℝ) ^ 2 + (tail / (rule.edges : ℝ) ^ 2) * ratio,
    hradius, hradiusCritical, hradiusOne, lt_min hnear hradius, min_le_right _ _, mul_pos hwindow (div_pos hlower (pow_pos hm _)),
    add_pos (div_pos hupper (pow_pos hm _)) (mul_pos (div_pos htailPositive (pow_pos hm _)) hratio), ?_⟩
  intro p hpAllowed hpNear
  obtain ⟨hp, hp', hpne⟩ := hallowed p hpAllowed
  have hpRadius : |p - critical| < radius := hpNear.trans_le (min_le_right _ _)
  have hdepthLarge := hdepth p hp hp' hpne (hpNear.trans_le (min_le_left _ _))
  have hbefore (j : ℕ) (hj : j < rule.reliabilityExitTime critical radius p) :
      |rule.network.reliability^[j] p - critical| < radius :=
    h.reliability_exit_before critical radius p hc hc' hfixed hradiusCritical hradiusOne hp hp' hpne j hj
  have hnonneg (n : ℕ) : 0 ≤ (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1) :=
    mul_nonneg (pow_nonneg (one_div_nonneg.mpr hm.le) _) (rule.expectedClusterBirthPower_nonneg hp.le hp'.le _ _)
  have hpre (n : ℕ) (hn : n < rule.reliabilityExitTime critical radius p) :
      (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1) ≤
        (upper / (rule.edges : ℝ) ^ 2) * ratio ^ n := by
    have hh := hupperBound p hp hp' n (fun j hj => (hbefore j (hj.trans_lt hn)).trans_le hradiusUpper)
    exact (mul_le_mul_of_nonneg_left hh (pow_nonneg (one_div_nonneg.mpr hm.le) _)).trans_eq
      (discounted_power_identity _ growth upper hm order n)
  have hpost := hpostBound p hpAllowed hpRadius
  have hscaledPost := rule.weighted_birth_tail_scaling p growth tail order
    (rule.reliabilityExitTime critical radius p) hm hpost.1 hpost.2
  have hfull := stopped_series_geometric_upper
    (fun n => (1 / (rule.edges : ℝ)) ^ (n + 2) * rule.expectedClusterBirthPower p order (n + 1))
    ratio (upper / (rule.edges : ℝ) ^ 2) (tail / (rule.edges : ℝ) ^ 2)
    (rule.reliabilityExitTime critical radius p) hratio
    (div_nonneg hupper.le (pow_nonneg hm.le _)) (div_nonneg htailPositive.le (pow_nonneg hm.le _))
    (by omega) hnonneg hpre hscaledPost.1 hscaledPost.2
  refine ⟨hfull.1, ?_, hfull.2⟩
  apply hwindowBound _ (lower / (rule.edges : ℝ) ^ 2)
    (div_nonneg hlower.le (pow_nonneg hm.le _)) hnonneg hfull.1 _ (by omega)
  intro n hn hlast
  have hh := hlowerBound p hp hp' n hn
    (fun j hj => (hbefore j (hj.trans_lt hlast)).trans_le hradiusLower)
  have hmultiply := mul_le_mul_of_nonneg_left hh (pow_nonneg (one_div_nonneg.mpr hm.le) (n + 2))
  change (1 / (rule.edges : ℝ)) ^ (n + 2) * (lower * growth ^ (order * n)) ≤ _ at hmultiply
  rw [discounted_power_identity _ growth lower hm order n] at hmultiply
  exact hmultiply

end
end Universality.Rule

import Universality.Percolation.CriticalRootSizeScaleBounds
import Universality.Analysis.GeometricSizeLogBound

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 0

/-- A uniform bounded logarithmic error for the actual critical root-size law. -/
theorem Classical.critical_root_size_probability_log_error {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ size : ℕ in atTop,
      0 < rule.limitingRootSizeProbability p size ∧
      |Real.log (rule.limitingRootSizeProbability p size) -
        (-Real.log (rule.edges : ℝ) /
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) *
            Real.log (size : ℝ)| ≤ bound := by
  let growth : ℝ := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  let scale : ℝ := 1 / ((rule.edges : ℝ) * growth)
  have hgrowth : 1 < growth :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hr : 0 < growth := zero_lt_one.trans hgrowth
  have hm : (0 : ℝ) < rule.edges := by exact_mod_cast (Nat.zero_lt_of_lt h.edges_gt_one)
  have hscale : 0 < scale := one_div_pos.mpr (mul_pos hm hr)
  have hlog : 0 < Real.log growth := Real.log_pos hgrowth
  obtain ⟨lower, upper, hlower, hupper, start, hb⟩ := h.critical_root_size_probability_scale_bounds p hp hp' hfixed
  have hcast : Tendsto (fun size : ℕ => (size : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ size : ℕ in atTop, 0 < rule.limitingRootSizeProbability p size ∧
      |Real.log (rule.limitingRootSizeProbability p size) -
        (1 + Real.log scale / Real.log growth) * Real.log (size : ℝ)| ≤
          |Real.log lower| + |Real.log upper| + |Real.log scale / Real.log growth| * Real.log growth := by
    filter_upwards [hcast.eventually (eventually_ge_atTop (1 : ℝ)),
      hcast.eventually (eventually_ge_atTop (growth ^ start)), eventually_gt_atTop rule.vertices]
      with size hsizeOne hsizeStart hsizeLarge
    obtain ⟨depth, hsizeLower, hsizeUpper⟩ := exists_nat_pow_near hsizeOne hgrowth
    have hdepth : start ≤ depth := by
      by_contra hn
      have hpower := pow_le_pow_right₀ hgrowth.le (show depth + 1 ≤ start by omega)
      exact (not_lt_of_ge (hpower.trans hsizeStart)) hsizeUpper
    have hpoint := hb depth hdepth size hsizeLarge hsizeLower hsizeUpper.le
    have hsizePos : (0 : ℝ) < size := zero_lt_one.trans_le hsizeOne
    refine ⟨(mul_pos hlower (mul_pos hsizePos (pow_pos hscale depth))).trans_le hpoint.1, ?_⟩
    exact size_scaled_geometric_log_error (rule.limitingRootSizeProbability p size) (size : ℝ)
      growth scale lower upper depth hsizePos hgrowth hscale hlower hupper hsizeLower hsizeUpper.le
      hpoint.1 hpoint.2
  have hvalue : 1 + Real.log scale / Real.log growth = -Real.log (rule.edges : ℝ) / Real.log growth := by
    dsimp [scale]
    rw [Real.log_div one_ne_zero (mul_ne_zero hm.ne' hr.ne'), Real.log_one, Real.log_mul hm.ne' hr.ne']
    field_simp [hlog.ne']
    <;> ring
  refine ⟨|Real.log lower| + |Real.log upper| +
    |Real.log scale / Real.log growth| * Real.log growth, by positivity, ?_⟩
  filter_upwards [hevent] with size hs
  refine ⟨hs.1, ?_⟩
  simpa only [hvalue] using hs.2

/-- Critical point-probability exponent of the actual thermodynamic root
size law. Identification with an infinite rooted graph remains separate. -/
theorem Classical.critical_root_size_probability_exponent {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    (∀ᶠ size : ℕ in atTop, 0 < rule.limitingRootSizeProbability p size) ∧
    Tendsto (fun size : ℕ => Real.log (rule.limitingRootSizeProbability p size) / Real.log (size : ℝ))
      atTop (𝓝 (-Real.log (rule.edges : ℝ) /
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))) := by
  obtain ⟨bound, _, hevent⟩ := h.critical_root_size_probability_log_error p hp hp' hfixed
  refine ⟨hevent.mono (fun _ hh => hh.1), ?_⟩
  exact tendsto_ratio_of_bounded_error_atTop atTop
    (fun size : ℕ => Real.log (rule.limitingRootSizeProbability p size))
    (fun size : ℕ => Real.log (size : ℝ)) _ bound
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) (hevent.mono (fun _ hh => hh.2))

end
end Universality.Rule

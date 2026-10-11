import Universality.Percolation.CriticalRootSizeExponent
import Universality.Analysis.PowerBoundsFromLogError
import Universality.Percolation.MassSpectralUpperBound

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- Genuine two-constant power bounds, stronger than the logarithmic
point-probability exponent alone. -/
theorem Classical.critical_root_size_probability_power_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ size : ℕ in atTop,
      lower * (size : ℝ) ^ (-Real.log (rule.edges : ℝ) /
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) ≤
          rule.limitingRootSizeProbability p size ∧
      rule.limitingRootSizeProbability p size ≤
        upper * (size : ℝ) ^ (-Real.log (rule.edges : ℝ) /
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) := by
  obtain ⟨bound, _, hb⟩ := h.critical_root_size_probability_log_error p hp hp' hfixed
  refine ⟨Real.exp (-bound), Real.exp bound, Real.exp_pos _, Real.exp_pos _, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with size hs hsize
  have hsizePos : (0 : ℝ) < size := by exact_mod_cast (show 0 < size by omega)
  exact rpow_bounds_of_log_error _ _ _ _ hs.1 hsizePos hs.2

/-- The inverse of the paper's delta is minus one minus the point-probability
logarithmic slope. It is positive because the mass growth is strictly below m. -/
theorem Classical.critical_inverse_delta {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    0 < (Real.log (rule.edges : ℝ) -
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ∧
    Tendsto (fun size : ℕ => -1 - Real.log (rule.limitingRootSizeProbability p size) / Real.log (size : ℝ))
      atTop (𝓝 ((Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))) := by
  have hgrowth : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hlog : 0 < Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) :=
    Real.log_pos hgrowth
  have hgap := Real.log_lt_log (zero_lt_one.trans hgrowth) (h.mass_spectralRadius_lt_edges p hp hp')
  refine ⟨div_pos (sub_pos.mpr hgap) hlog, ?_⟩
  have hh : Tendsto
      (fun size : ℕ => (-1 : ℝ) - Real.log (rule.limitingRootSizeProbability p size) / Real.log (size : ℝ))
      atTop (𝓝 ((-1 : ℝ) - -Real.log (rule.edges : ℝ) /
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))) :=
    tendsto_const_nhds.sub (h.critical_root_size_probability_exponent p hp hp' hfixed).2
  have heq : (-1 : ℝ) - -Real.log (rule.edges : ℝ) /
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) =
      (Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) := by
    field_simp [hlog.ne']
    <;> ring
  simpa only [heq] using hh

/-- Explicit delta value in the convention used by the paper. -/
theorem Classical.critical_delta_value {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    0 < Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
      (Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) ∧
    Tendsto (fun size : ℕ => -1 - Real.log (rule.limitingRootSizeProbability p size) / Real.log (size : ℝ))
      atTop (𝓝 (1 / (Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        (Real.log (rule.edges : ℝ) -
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))))) := by
  have hh := h.critical_inverse_delta p hp hp' hfixed
  constructor
  · simpa only [inv_div] using (inv_pos.mpr hh.1)
  · simpa only [one_div, inv_div] using hh.2

end
end Universality.Rule

import Universality.Percolation.ActualBirthDomination
import Universality.Percolation.GeometricBirthContinuity
import Universality.Percolation.MassSpectralLowerBound

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.supercritical_root_moment_tendsto_critical {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) < rule.edges) :
    Tendsto (fun p : ℝ => (rule.limitingRootSizeMoment p order).toReal)
      (𝓝[Set.Ioi critical] critical) (𝓝 (rule.limitingRootSizeMoment critical order).toReal) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hmpos : (0 : ℝ) < rule.edges := zero_lt_one.trans hm
  have hfirst : 0 ≤ ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges := by positivity
  have hfirstOne : ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges < 1 :=
    (div_lt_one hmpos).mpr hthreshold
  have hlater : 0 ≤ (1 / 2 : ℝ) / rule.edges := by positivity
  have hlaterOne : (1 / 2 : ℝ) / rule.edges < 1 := by
    apply (div_lt_one hmpos).mpr
    linarith
  refine h.root_moment_tendsto_of_geometric_birth_bound critical hc hc' hfixed order hthreshold
    (𝓝[Set.Ioi critical] critical) (tendsto_id'.mpr nhdsWithin_le_nhds)
    (fun p => critical < p ∧ p < 1) ?_ ?_
    (max (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)
      ((1 / 2 : ℝ) / rule.edges)) ?_ ?_ ?_
  · intro p hp
    exact ⟨hc.trans hp.1, hp.2⟩
  · have hupper : ∀ᶠ p in 𝓝 critical, p < 1 := Iio_mem_nhds hc'
    filter_upwards [self_mem_nhdsWithin, hupper.filter_mono nhdsWithin_le_nhds] with p hp hu
    exact ⟨hp, hu⟩
  · exact hfirst.trans (le_max_left _ _)
  · exact max_lt hfirstOne hlaterOne
  · exact h.supercritical_nearcritical_birth_domination critical hc hc' hfixed (order + 1) (by omega)

theorem Classical.subcritical_root_moment_tendsto_critical {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) < rule.edges) :
    Tendsto (fun p : ℝ => (rule.limitingRootSizeMoment p order).toReal)
      (𝓝[Set.Iio critical] critical) (𝓝 (rule.limitingRootSizeMoment critical order).toReal) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hmpos : (0 : ℝ) < rule.edges := zero_lt_one.trans hm
  have hfirst : 0 ≤ ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges := by positivity
  have hfirstOne : ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges < 1 :=
    (div_lt_one hmpos).mpr hthreshold
  have hlater : 0 ≤ (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) / rule.edges := by positivity
  have hlaterOne : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) / rule.edges < 1 := by
    apply (div_lt_one hmpos).mpr
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (h.terminal_degree_lt_mass_spectralRadius critical hc hc').le (order + 1)).trans_lt hthreshold
  refine h.root_moment_tendsto_of_geometric_birth_bound critical hc hc' hfixed order hthreshold
    (𝓝[Set.Iio critical] critical) (tendsto_id'.mpr nhdsWithin_le_nhds)
    (fun p => 0 < p ∧ p < critical) ?_ ?_
    (max (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)
      ((rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) / rule.edges)) ?_ ?_ ?_
  · intro p hp
    exact ⟨hp.1, hp.2.trans hc'⟩
  · have hlower : ∀ᶠ p in 𝓝 critical, 0 < p := Ioi_mem_nhds hc
    filter_upwards [self_mem_nhdsWithin, hlower.filter_mono nhdsWithin_le_nhds] with p hp hl
    exact ⟨hl, hp⟩
  · exact hfirst.trans (le_max_left _ _)
  · exact max_lt hfirstOne hlaterOne
  · exact h.subcritical_nearcritical_birth_domination critical hc hc' hfixed (order + 1) (by omega)

end
end Universality.Rule

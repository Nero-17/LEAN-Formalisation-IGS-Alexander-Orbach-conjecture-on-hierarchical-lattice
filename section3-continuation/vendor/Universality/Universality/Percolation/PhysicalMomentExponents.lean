import Universality.Percolation.ActualSusceptibilityExponent
import Universality.Percolation.ActualMomentGap
import Universality.Percolation.SubcriticalHighMomentDivergence
import Universality.Percolation.PhysicalObservables
import Universality.Percolation.AnnealedSupercriticalMomentFinite

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
attribute [local irreducible] limitingRootSizeMoment physicalFiniteClusterMoment

/-- The physical infinite-root finite-cluster moment and the thermodynamic
size-law moment agree throughout a neighborhood of the interior critical point. -/
theorem Classical.physical_moment_eventuallyEq {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1) (order : ℕ) :
    (fun p => rule.physicalFiniteClusterMoment h.edges_gt_one p order) =ᶠ[𝓝 critical]
      (fun p => rule.limitingRootSizeMoment p order) := by
  filter_upwards [Ioi_mem_nhds hc, Iio_mem_nhds hc'] with p hp hp'
  exact rule.physicalFiniteClusterMoment_eq h.edges_gt_one h.vertices_gt_two hp.le hp'.le order

theorem Classical.physical_supercritical_susceptibility_exponent {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Tendsto (fun p : ℝ => -(Real.log (rule.physicalFiniteClusterMoment h.edges_gt_one p 1).toReal /
      Real.log |p - critical|)) (𝓝[>] critical)
      (𝓝 (max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ 2 / rule.edges)) 0 / Real.log (deriv rule.network.reliability critical))) := by
  apply (h.supercritical_susceptibility_exponent critical hc hc' hfixed).congr'
  filter_upwards [(h.physical_moment_eventuallyEq critical hc hc' 1).filter_mono nhdsWithin_le_nhds] with p hp
  rw [hp]

theorem Classical.physical_subcritical_susceptibility_exponent {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ 2 < rule.edges) :
    Tendsto (fun p : ℝ => -(Real.log (rule.physicalFiniteClusterMoment h.edges_gt_one p 1).toReal /
      Real.log |p - critical|)) (𝓝[<] critical)
      (𝓝 (max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ 2 / rule.edges)) 0 / Real.log (deriv rule.network.reliability critical))) := by
  apply (h.subcritical_susceptibility_exponent critical hc hc' hfixed hthreshold).congr'
  filter_upwards [(h.physical_moment_eventuallyEq critical hc hc' 1).filter_mono nhdsWithin_le_nhds] with p hp
  rw [hp]

theorem Classical.physical_supercritical_moment_ratio_exponent {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) :
    Tendsto (fun p : ℝ => -(Real.log
      ((rule.physicalFiniteClusterMoment h.edges_gt_one p (order + 1)).toReal /
        (rule.physicalFiniteClusterMoment h.edges_gt_one p order).toReal) / Real.log |p - critical|))
      (𝓝[>] critical)
      (𝓝 ((max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 2) / rule.edges)) 0 -
        max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)) 0) / Real.log (deriv rule.network.reliability critical))) := by
  apply (h.supercritical_root_moment_ratio_log_rate critical hc hc' hfixed order).congr'
  filter_upwards [(h.physical_moment_eventuallyEq critical hc hc' order).filter_mono nhdsWithin_le_nhds,
    (h.physical_moment_eventuallyEq critical hc hc' (order + 1)).filter_mono nhdsWithin_le_nhds] with p hp hp'
  rw [hp, hp']

theorem Classical.physical_subcritical_moment_ratio_exponent {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 2) < rule.edges) :
    Tendsto (fun p : ℝ => -(Real.log
      ((rule.physicalFiniteClusterMoment h.edges_gt_one p (order + 1)).toReal /
        (rule.physicalFiniteClusterMoment h.edges_gt_one p order).toReal) / Real.log |p - critical|))
      (𝓝[<] critical)
      (𝓝 ((max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 2) / rule.edges)) 0 -
        max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)) 0) / Real.log (deriv rule.network.reliability critical))) := by
  apply (h.subcritical_root_moment_ratio_log_rate critical hc hc' hfixed order hthreshold).congr'
  filter_upwards [(h.physical_moment_eventuallyEq critical hc hc' order).filter_mono nhdsWithin_le_nhds,
    (h.physical_moment_eventuallyEq critical hc hc' (order + 1)).filter_mono nhdsWithin_le_nhds] with p hp hp'
  rw [hp, hp']

theorem Classical.physical_supercritical_all_moment_gaps_common_iff {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    (∀ order : ℕ, 1 ≤ order →
      Tendsto (fun p : ℝ => -(Real.log
        ((rule.physicalFiniteClusterMoment h.edges_gt_one p (order + 1)).toReal /
          (rule.physicalFiniteClusterMoment h.edges_gt_one p order).toReal) / Real.log |p - critical|))
        (𝓝[>] critical) (𝓝 (Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / Real.log (deriv rule.network.reliability critical)))) ↔
      (rule.edges : ℝ) ≤ ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ 2 := by
  rw [← h.supercritical_all_root_moment_gaps_common_iff critical hc hc' hfixed]
  constructor
  · intro hall order horder
    apply (hall order horder).congr'
    filter_upwards [(h.physical_moment_eventuallyEq critical hc hc' order).filter_mono nhdsWithin_le_nhds,
      (h.physical_moment_eventuallyEq critical hc hc' (order + 1)).filter_mono nhdsWithin_le_nhds] with p hp hp'
    rw [hp, hp']
  · intro hall order horder
    apply (hall order horder).congr'
    filter_upwards [(h.physical_moment_eventuallyEq critical hc hc' order).filter_mono nhdsWithin_le_nhds,
      (h.physical_moment_eventuallyEq critical hc hc' (order + 1)).filter_mono nhdsWithin_le_nhds] with p hp hp'
    rw [hp, hp']

theorem Classical.physical_supercritical_eventually_moment_ratio_common {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∀ᶠ order : ℕ in atTop,
      Tendsto (fun p : ℝ => -(Real.log
        ((rule.physicalFiniteClusterMoment h.edges_gt_one p (order + 1)).toReal /
          (rule.physicalFiniteClusterMoment h.edges_gt_one p order).toReal) / Real.log |p - critical|))
        (𝓝[>] critical) (𝓝 (Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / Real.log (deriv rule.network.reliability critical))) := by
  filter_upwards [h.supercritical_eventually_root_moment_ratio_common critical hc hc' hfixed] with order hh
  apply hh.congr'
  filter_upwards [(h.physical_moment_eventuallyEq critical hc hc' order).filter_mono nhdsWithin_le_nhds,
    (h.physical_moment_eventuallyEq critical hc hc' (order + 1)).filter_mono nhdsWithin_le_nhds] with p hp hp'
  rw [hp, hp']

theorem Classical.physical_subcritical_eventually_moment_eq_top {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    ∀ᶠ order : ℕ in atTop, rule.physicalFiniteClusterMoment h.edges_gt_one p order = ⊤ := by
  filter_upwards [h.subcritical_eventually_root_moment_eq_top critical p hc hc' hfixed hp hpc] with order hh
  rw [rule.physicalFiniteClusterMoment_eq h.edges_gt_one h.vertices_gt_two hp.le (hpc.trans hc').le]
  exact hh


theorem Classical.physical_supercritical_moment_ne_top {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hpc : critical < p) (hp' : p ≤ 1)
    (order : ℕ) : rule.physicalFiniteClusterMoment h.edges_gt_one p order ≠ ⊤ := by
  rw [rule.physicalFiniteClusterMoment_eq h.edges_gt_one h.vertices_gt_two (hc.trans hpc).le hp']
  exact h.supercritical_root_moment_ne_top critical p hc hc' hfixed hpc hp' order

theorem Classical.physical_subcritical_moment_finite_iff {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical)
    (order : ℕ) :
    rule.physicalFiniteClusterMoment h.edges_gt_one p order ≠ ⊤ ↔
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) < rule.edges := by
  rw [rule.physicalFiniteClusterMoment_eq h.edges_gt_one h.vertices_gt_two hp.le (hpc.trans hc').le]
  exact h.subcritical_root_moment_finite_iff critical p hc hc' hfixed hp hpc order

end
end Universality.Rule

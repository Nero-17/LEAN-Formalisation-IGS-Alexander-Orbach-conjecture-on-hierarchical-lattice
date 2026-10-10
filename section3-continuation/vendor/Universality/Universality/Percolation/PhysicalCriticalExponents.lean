import Universality.Percolation.PhysicalObservables
import Universality.Percolation.EscapingRootMassExponent
import Universality.Percolation.CriticalRootSizePowerBounds

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable {rule : Rule} [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]

theorem Classical.physical_beta_exponent (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Tendsto (fun p : ℝ => Real.log (rule.physicalInfiniteClusterProbability h.edges_gt_one p) /
      Real.log (p - critical)) (𝓝[>] critical)
      (𝓝 ((Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)) /
        Real.log (deriv rule.network.reliability critical))) := by
  apply (h.escaping_root_mass_exponent critical hc hc' hfixed).congr'
  have hunit : ∀ᶠ p : ℝ in 𝓝[>] critical, p < 1 :=
    (gt_mem_nhds hc').filter_mono nhdsWithin_le_nhds
  filter_upwards [hunit, self_mem_nhdsWithin] with p hp hpc
  rw [rule.physicalInfiniteClusterProbability_eq h.edges_gt_one h.vertices_gt_two
    (hc.trans hpc).le hp.le]

theorem Classical.physical_delta_exponent (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    (∀ᶠ size : ℕ in atTop, 0 < rule.physicalFiniteClusterProbability h.edges_gt_one critical size) ∧
    Tendsto (fun size : ℕ => -1 - Real.log (rule.physicalFiniteClusterProbability h.edges_gt_one critical size) /
      Real.log (size : ℝ)) atTop
      (𝓝 ((Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)) /
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal))) := by
  simp only [rule.physicalFiniteClusterProbability_eq h.edges_gt_one h.vertices_gt_two hc.le hc'.le]
  exact ⟨(h.critical_root_size_probability_exponent critical hc hc' hfixed).1,
    (h.critical_inverse_delta critical hc hc' hfixed).2⟩

end
end Universality.Rule

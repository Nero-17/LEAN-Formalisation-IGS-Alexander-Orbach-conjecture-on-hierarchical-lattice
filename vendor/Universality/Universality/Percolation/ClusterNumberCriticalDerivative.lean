import Universality.Percolation.ClusterNumberLinearRemainder

namespace Universality.FiniteNetwork
noncomputable section

/-- Real extension used solely to state ordinary derivatives at interior
parameters. On the physical parameter interval this is the actual density. -/
def clusterNumberDensityExtension {vertices edges : ℕ} (R : FiniteNetwork vertices edges) (p : ℝ) : ℝ :=
  if hp : p ∈ Set.Icc (0 : ℝ) 1 then R.clusterNumberSeries ⟨p, hp⟩ else 0

theorem clusterNumberDensityExtension_eq {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : Set.Icc (0 : ℝ) 1) :
    R.clusterNumberDensityExtension p.val = R.clusterNumberSeries p := by
  simp [clusterNumberDensityExtension, p.property]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open Filter FiniteNetwork
open scoped Topology

/-- The first derivative of the actual density exists at the critical point.
This does not assert neighborhood `C¹` regularity. -/
theorem Classical.cluster_number_hasDerivAt_critical {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    HasDerivAt rule.network.clusterNumberDensityExtension
      ((((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
          (rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).derivative.eval critical) /
        ((rule.edges : ℝ) - deriv rule.network.reliability critical)) critical := by
  obtain ⟨coefficient, bound, _, hcoefficient, hbound⟩ :=
    h.cluster_number_linear_remainder critical hc hc' hfixed
  have hrepelling := rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale
  have hsquare := rule.network.pivotal_response_sq_lt_edges critical hc hc' hfixed h.scale
  have hgap : (rule.edges : ℝ) - deriv rule.network.reliability critical ≠ 0 := by nlinarith
  have hcoefficientValue : coefficient =
      (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
        (rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).derivative.eval critical) /
      ((rule.edges : ℝ) - deriv rule.network.reliability critical) := by
    apply (eq_div_iff hgap).mpr
    simpa only [mul_comm] using hcoefficient
  rw [← hcoefficientValue]
  apply hasDerivAt_of_quadratic_remainder _ critical coefficient bound
  filter_upwards [Ioo_mem_nhds hc hc'] with p hp
  have hpclosed : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have hcenter : critical ∈ Set.Icc (0 : ℝ) 1 := ⟨hc.le, hc'.le⟩
  simpa only [clusterNumberDensityExtension, dif_pos hpclosed, dif_pos hcenter] using
    hbound ⟨p, hpclosed⟩

end
end Universality.Rule

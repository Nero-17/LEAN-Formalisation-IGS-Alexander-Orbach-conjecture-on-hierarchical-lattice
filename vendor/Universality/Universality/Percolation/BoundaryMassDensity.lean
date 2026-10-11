import Universality.Percolation.MassSpectralUpperBound
import Universality.Percolation.VertexMassGrowth
import Universality.Percolation.ClassicalClusterNumber

namespace Universality.Rule
noncomputable section
open Filter FiniteNetwork
open scoped Topology
set_option maxHeartbeats 0

/-- Each actual conditional internal boundary mass occupies an asymptotically
zero fraction of the finite graph. This alone is not yet the infinite-volume
assertion that the critical root cluster is almost surely finite. -/
theorem Classical.conditional_boundary_mass_density_tendsto_zero {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (state : LiveState) :
    Tendsto (fun n : ℕ => (rule.generation n).network.conditionalVertexMass p state /
      ((rule.generation n).vertices : ℝ)) atTop (𝓝 0) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := h.internal_vertex_mass_bounds p hp hp' hfixed
  have hpositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).1.trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  have hratio := tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg hpositive.le (lt_trans zero_lt_one hm).le)
    ((div_lt_one (lt_trans zero_lt_one hm)).mpr (h.mass_spectralRadius_lt_edges p hp hp'))
  have hnormal : Tendsto (fun n : ℕ => (rule.generation n).network.conditionalVertexMass p state /
      (rule.edges : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n => upper / (rule.edges : ℝ) *
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal / rule.edges) ^ n)
    · intro n
      exact div_nonneg ((rule.generation n).network.conditionalInternalMean_nonneg p hp.le hp'.le _ _ _)
        (pow_pos (lt_trans zero_lt_one hm) _).le
    · intro n
      calc
        _ ≤ upper * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n /
            (rule.edges : ℝ) ^ (n + 1) :=
          div_le_div_of_nonneg_right (hbounds n state).2 (pow_pos (lt_trans zero_lt_one hm) _).le
        _ = _ := by rw [div_pow, pow_succ]; ring
    · simpa using hratio.const_mul (upper / (rule.edges : ℝ))
  have hlimit := hnormal.div (rule.generation_volume_ratio_tendsto h.edges_gt_one)
    (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)).ne'
  simp only [zero_div] at hlimit
  convert hlimit using 1
  ext n
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (pow_ne_zero _ (lt_trans zero_lt_one hm).ne')]

end
end Universality.Rule

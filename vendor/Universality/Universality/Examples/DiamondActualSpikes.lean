import Universality.Examples.DiamondSpikeExpectation
import Universality.Percolation.RadiusPointEquivalence
import Universality.Percolation.RadiusPointTransfer
import Universality.Percolation.VertexMassGrowth

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def diamondDoubleTopDecomposition (n : ℕ) :
    (diamondRule.generation (n + 2)).network.NetworkEquivalence
      (diamondNetwork.substitute (diamondNetwork.substitute (diamondRule.generation n).network)) :=
  (diamondRule.generationTopDecomposition (n + 1)).trans
    ((NetworkEquivalence.refl diamondNetwork).substitute (diamondRule.generationTopDecomposition n))

def diamondSpikeDecomposition (n : ℕ) :
    (diamondRule.generation (1 + (n + 2) + 1)).network.NetworkEquivalence
      ((diamondRule.generation 1).network.substitute
        (diamondNetwork.substitute (diamondNetwork.substitute (diamondRule.generation n).network))) :=
  (diamondRule.generationBlockDecomposition 1 (n + 2)).trans
    ((NetworkEquivalence.refl (diamondRule.generation 1).network).substitute (diamondDoubleTopDecomposition n))

/-- Fixed-probability isolated cells force genuine dyadic spikes in the
annealed limiting radius point law of the actual diamond rule. -/
theorem diamond_actual_radius_spikes
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : diamondNetwork.reliability p = p) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ n,
      constant * (((spectralRadius ℂ ((diamondNetwork.massMatrix p).map Complex.ofReal)).toReal) / 4) ^ n ≤
        diamondRule.limitingRootRadiusProbability p (2 ^ (n + 3)) := by
  obtain ⟨edge, hs, ht, hs', ht'⟩ := diamondRule_classical.second_generation_internal_edge
  obtain ⟨constant, upper, hconstant, hupper, hmass⟩ :=
    diamondRule_classical.internal_vertex_mass_bounds p hp hp' hfixed
  have hweight : 0 < bernoulliWeight p (onlyOpen edge) ^ 16 := pow_pos (bernoulliWeight_pos hp hp' _) _
  refine ⟨(3 / 2 : ℝ) * (bernoulliWeight p (onlyOpen edge) ^ 16 * constant / 4 ^ 5), by positivity, ?_⟩
  intro n
  have hlength : 4 * (diamondRule.generation n).network.fullGraph.dist
      (diamondRule.generation n).network.source (diamondRule.generation n).network.target = 2 ^ (n + 3) := by
    rw [diamond_generation_terminal_distance, show n + 3 = (n + 1) + 2 by omega]
    simp only [pow_add]
    norm_num
    omega
  have hdiameter (u v) : (diamondRule.generation n).network.fullGraph.dist u v ≤
      (diamondRule.generation n).network.fullGraph.dist
        (diamondRule.generation n).network.source (diamondRule.generation n).network.target := by
    rw [diamond_generation_terminal_distance]
    exact diamond_generation_diameter n u v
  have hgeodesic (configuration) (hcrossing) := diamond_generation_open_geodesic n configuration hcrossing
  have hgeodesic' : ∀ configuration, (diamondRule.generation n).network.crosses configuration = true →
      ∃ walk : ((diamondRule.generation n).network.openGraph configuration).Walk
        (diamondRule.generation n).network.source (diamondRule.generation n).network.target,
        walk.length = (diamondRule.generation n).network.fullGraph.dist
          (diamondRule.generation n).network.source (diamondRule.generation n).network.target := by
    intro configuration hcrossing
    simpa only [diamond_generation_terminal_distance] using hgeodesic configuration hcrossing
  have hexpectation := diamond_spike_expectation (diamondRule.generation 1).network (diamondRule.generation n).network
    (diamondRule_classical.generation 1).connected (diamondRule_classical.generation n).connected
    (diamond_generation_terminal_distance_sum n) hdiameter
    (by rw [diamond_generation_terminal_distance]; positivity) hgeodesic' edge hs ht hs' ht' hp.le hp'.le
    (by rwa [diamondRule.generation_fixed_point p hfixed]) (by rwa [diamondRule.generation_fixed_point p hfixed])
  rw [diamondRule.generation_fixed_point p hfixed, hlength] at hexpectation
  rw [(diamondSpikeDecomposition n).expectedInternalRadiusPointRootCount
    (diamondRule_classical.generation (1 + (n + 2) + 1)).connected] at hexpectation
  have hfinite := (mul_le_mul_of_nonneg_left (hmass n .connected).1 hweight.le).trans hexpectation
  have htransfer := diamondRule_classical.internal_radius_point_expectation_le_limit hp.le hp'.le
    (2 ^ (n + 3)) (1 + (n + 2) + 1)
  have hnormalization : (((diamondRule.edges : ℝ) - 1) / ((diamondRule.vertices : ℝ) - 2)) = (3 / 2 : ℝ) := by
    change ((4 : ℝ) - 1) / ((4 : ℝ) - 2) = 3 / 2
    norm_num
  rw [hnormalization] at htransfer
  have hscaled := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hfinite (show (0 : ℝ) ≤ 4 ^ (1 + (n + 2) + 1 + 1) by positivity))
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  apply le_trans _ htransfer
  change _ ≤ (3 / 2 : ℝ) *
    ((diamondRule.generation (1 + (n + 2) + 1)).network.expectedInternalRadiusPointRootCount p (2 ^ (n + 3)) /
      (4 : ℝ) ^ (1 + (n + 2) + 1 + 1))
  calc
    _ = (3 / 2 : ℝ) * (bernoulliWeight p (onlyOpen edge) ^ 16 *
        (constant * (spectralRadius ℂ ((diamondNetwork.massMatrix p).map Complex.ofReal)).toReal ^ n) /
        4 ^ (1 + (n + 2) + 1 + 1)) := by
      rw [show 1 + (n + 2) + 1 + 1 = n + 5 by omega, pow_add, div_pow]
      field_simp
      <;> ring
    _ ≤ _ := hscaled

end
end Universality



import Universality.Percolation.AnnealedFiniteBirthMoments
import Universality.Percolation.VertexMeanLimit

namespace Universality.Rule
noncomputable section
open Filter FiniteNetwork
open scoped Topology

theorem generation_internal_cluster_mass_recursion (rule : Rule) (p : ℝ) (n : ℕ) :
    (rule.generation (n + 1)).network.expectedInternalClusterMass p =
      (rule.edges : ℝ) * (rule.generation n).network.expectedInternalClusterMass p +
        rule.expectedClusterBirthPower p 1 (n + 1) := by
  have hs := (((rule.generation n).network.hasSum_size_expectedInternalClusterCount p).mul_left
    (rule.edges : ℝ)).add (rule.expectedClusterBirthPower_hasSum p 1 (n + 1))
  have hidentity (size : ℕ) : (rule.edges : ℝ) *
      ((size : ℝ) * (rule.generation n).network.expectedInternalClusterCount p size) +
      (size : ℝ) ^ 1 * rule.expectedClusterBirth p size (n + 1) =
      (size : ℝ) * (rule.generation (n + 1)).network.expectedInternalClusterCount p size := by
    rw [rule.generation_expectedInternalClusterCount]
    simp only [expectedClusterBirth, pow_one]
    ring
  exact ((rule.generation (n + 1)).network.hasSum_size_expectedInternalClusterCount p).unique
    (hs.congr_fun (fun size => (hidentity size).symm))

theorem expectedClusterBirthPower_one_boundary_difference (rule : Rule) (p : ℝ) (n : ℕ) :
    rule.expectedClusterBirthPower p 1 (n + 1) =
      (rule.vertices : ℝ) - 2 +
        (rule.edges : ℝ) * (rule.generation n).network.expectedInternalBoundaryMass p -
          (rule.generation (n + 1)).network.expectedInternalBoundaryMass p := by
  have hmass := rule.generation_internal_cluster_mass_recursion p n
  have hbefore := (rule.generation n).network.expectedInternalClusterMass_partition p
  have hafter := (rule.generation (n + 1)).network.expectedInternalClusterMass_partition p
  have hvertices : (rule.generation (n + 1)).vertices =
      rule.vertices + rule.edges * ((rule.generation n).vertices - 2) := by
    have hc := Fintype.card_congr (rule.generationTopDecomposition n).vertex
    simpa only [Fintype.card_fin, FiniteNetwork.card_substitution_vertices] using hc
  have hcast := congrArg (fun value : ℕ => (value : ℝ)) hvertices
  push_cast [Nat.cast_sub (rule.generation n).network.two_le_vertices] at hcast
  nlinarith

theorem Classical.boundary_mass_normalized_mean_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : ℝ, 0 < limit ∧ Tendsto (fun n : ℕ =>
      (rule.generation n).network.expectedInternalBoundaryMass p /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      atTop (𝓝 limit) := by
  obtain ⟨limit, hpositive, heigen, hlimit⟩ := h.internal_vertex_mean_limit p hp hp' hfixed
  refine ⟨p * limit .connected + (1 - p) * limit .both,
    add_pos (mul_pos hp (hpositive _)) (mul_pos (sub_pos.mpr hp') (hpositive _)), ?_⟩
  have hs := ((hlimit .connected).const_mul p).add ((hlimit .both).const_mul (1 - p))
  convert hs using 1
  ext n
  rw [(rule.generation n).network.expectedInternalBoundaryMass_disintegrate p
    (by rwa [rule.generation_fixed_point p hfixed])
    (by rwa [rule.generation_fixed_point p hfixed]), rule.generation_fixed_point p hfixed]
  ring

/-- Actual critical birth mass has a strictly positive spectral-scale limit.
The coefficient is positive because the true mass spectral radius is below
the number of substitution edges. -/
theorem Classical.birth_first_moment_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : ℝ, 0 < limit ∧ Tendsto (fun n : ℕ =>
      rule.expectedClusterBirthPower p 1 (n + 1) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      atTop (𝓝 limit) := by
  obtain ⟨limit, hpositive, hlimit⟩ := h.boundary_mass_normalized_mean_limit p hp hp' hfixed
  have hradius : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hne : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ≠ 0 :=
    (lt_trans zero_lt_one hradius).ne'
  refine ⟨((rule.edges : ℝ) -
    (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * limit,
    mul_pos (sub_pos.mpr (h.mass_spectralRadius_lt_edges p hp hp')) hpositive, ?_⟩
  have hconstant : Tendsto (fun n : ℕ => ((rule.vertices : ℝ) - 2) /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      atTop (𝓝 0) := by
    simpa only [one_div_pow, mul_one_div, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (one_div_nonneg.mpr (lt_trans zero_lt_one hradius).le)
        ((div_lt_one (lt_trans zero_lt_one hradius)).mpr hradius)).const_mul ((rule.vertices : ℝ) - 2)
  have hnext := (hlimit.comp (tendsto_add_atTop_nat 1)).const_mul
    (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hs := (hconstant.add (hlimit.const_mul (rule.edges : ℝ))).sub hnext
  have heq (n : ℕ) : rule.expectedClusterBirthPower p 1 (n + 1) /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n =
      ((rule.vertices : ℝ) - 2) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n +
        (rule.edges : ℝ) * ((rule.generation n).network.expectedInternalBoundaryMass p /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) -
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
          ((rule.generation (n + 1)).network.expectedInternalBoundaryMass p /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1)) := by
    rw [rule.expectedClusterBirthPower_one_boundary_difference, pow_succ]
    field_simp [hne]
    <;> ring
  convert hs using 1
  · ext n
    exact heq n
  · congr 1
    ring

end
end Universality.Rule

import Universality.Percolation.AnnealedBirthFirstMoment
import Universality.Probability.FiniteRandomFamilyMoment

namespace Universality.FiniteNetwork
noncomputable section
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem birthClusterFamily_card_le_vertices (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) (configuration : Fin outerEdges → Configuration innerEdges) :
    (R.birthClusterFamily S configuration).card ≤ outerVertices := by
  have hsubset : R.birthClusterFamily S configuration ⊆ R.coarseTouchedClusters S configuration := by
    intro cluster hcluster
    obtain ⟨hinternal, htouch⟩ := Finset.mem_filter.mp hcluster
    obtain ⟨hfamily, hs, ht⟩ := Finset.mem_filter.mp hinternal
    rw [R.coarseTouchedClusters_eq]
    obtain ⟨vertex, hvertex, hcoarse⟩ := Finset.not_disjoint_iff.mp htouch
    exact Finset.mem_filter.mpr ⟨hfamily, vertex, hcoarse, hvertex⟩
  calc
    _ ≤ (R.coarseTouchedClusters S configuration).card := Finset.card_le_card hsubset
    _ = (R.clusterFamily (S.coarseConfiguration configuration)).card := R.coarseTouchedClusters_card S configuration
    _ ≤ outerVertices := by exact Finset.card_image_le.trans_eq (by simp)

theorem expectedBirthClusterPower_mean_pow_le (R : FiniteNetwork outerVertices outerEdges)
    (S : FiniteNetwork innerVertices innerEdges) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (order : ℕ) (horder : 1 ≤ order) :
    R.expectedBirthClusterPower S p 1 ^ order ≤ (outerVertices : ℝ) ^ (order - 1) *
      R.expectedBirthClusterPower S p order := by
  have h := finite_random_family_moment
    (bernoulliWeight p : Configuration (outerEdges * innerEdges) → ℝ)
    (fun configuration => R.birthClusterFamily S (substitutionConfigurationEquiv.symm configuration))
    (fun _ cluster => (cluster.card : ℝ)) (bernoulliWeight_nonneg hp hp') (sum_bernoulliWeight p)
    (fun _ _ _ => Nat.cast_nonneg _) outerVertices
    (fun configuration => R.birthClusterFamily_card_le_vertices S _) order horder
  simpa only [expectedBirthClusterPower, pow_one] using h

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.birth_moment_eventual_lower_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ᶠ n : ℕ in atTop,
      lower * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order * n) ≤
        rule.expectedClusterBirthPower p order (n + 1) := by
  obtain ⟨limit, hpositive, hlimit⟩ := h.birth_first_moment_limit p hp hp' hfixed
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).1.trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hvertices : (0 : ℝ) < rule.vertices := by
    have := h.vertices_gt_two
    exact_mod_cast (by omega : 0 < rule.vertices)
  refine ⟨(limit / 2) ^ order / (rule.vertices : ℝ) ^ (order - 1),
    div_pos (pow_pos (half_pos hpositive) _) (pow_pos hvertices _), ?_⟩
  filter_upwards [hlimit.eventually (Ioi_mem_nhds (half_lt_self hpositive))] with n hn
  have hmean : (limit / 2) *
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n ≤
      rule.expectedClusterBirthPower p 1 (n + 1) :=
    ((lt_div_iff₀ (pow_pos hradius n)).mp hn).le
  have hpower := pow_le_pow_left₀ (mul_nonneg (half_pos hpositive).le (pow_nonneg hradius.le _)) hmean order
  have hjensen := rule.network.expectedBirthClusterPower_mean_pow_le
    (rule.generation n).network hp.le hp'.le order horder
  change rule.expectedClusterBirthPower p 1 (n + 1) ^ order ≤
    (rule.vertices : ℝ) ^ (order - 1) * rule.expectedClusterBirthPower p order (n + 1) at hjensen
  calc
    _ = ((limit / 2) *
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ order /
          (rule.vertices : ℝ) ^ (order - 1) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm n order]
      ring
    _ ≤ _ := (div_le_iff₀ (pow_pos hvertices (order - 1))).mpr
      (by simpa only [mul_comm (rule.expectedClusterBirthPower p order (n + 1))] using hpower.trans hjensen)

end
end Universality.Rule

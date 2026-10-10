import Universality.Percolation.StrictReliability
import Universality.Percolation.PivotalDimension
import Universality.Percolation.ExactMassExpansion
import Universality.Matrix.RealDiagonalization

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

/-- An interior fixed point supplies the connectivity and deletion hypotheses
needed for the finite mass theory. This does not identify an infinite-volume
percolation threshold. -/
theorem interior_fixed_point_geometry (rule : Rule) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    rule.network.fullGraph.Reachable rule.network.source rule.network.target ∧
      (∀ edge, rule.network.crosses (onlyClosed edge) = true) ∧
      0 < deriv rule.network.reliability p := by
  have hconnected := (rule.network.reliability_pos_iff_connected hp hp').mp
    (by rwa [hfixed])
  exact ⟨hconnected,
    rule.network.interior_fixed_point_survives_single_deletion p hp hp' hfixed hscale,
    rule.network.reliability_derivative_pos hp hp' hconnected⟩

/-- Finite ambient edge growth, not a claim about Hausdorff dimension. -/
theorem finite_edge_growth_formula (rule : Rule)
    (hconnected : rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (n : ℕ) :
    Real.log ((rule.generation n).edges : ℝ) /
      Real.log ((rule.generation n).network.fullGraph.dist
        (rule.generation n).network.source (rule.generation n).network.target) =
      Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) := by
  rw [generation_terminal_distance rule hconnected, generation_edges,
    Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  exact mul_div_mul_left _ _ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)

/-- Three growth formulas from an interior fixed point, terminal symmetry and
terminal distance at least two. Every numerator on the left is defined on the
actual finite graph, rather than by the proposed formula on the right. -/
theorem finite_three_growth_formulas (rule : Rule) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (hsymmetric : rule.TerminalSymmetric)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    (∀ n : ℕ, Real.log ((rule.generation n).edges : ℝ) /
      Real.log ((rule.generation n).network.fullGraph.dist
        (rule.generation n).network.source (rule.generation n).network.target) =
      Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)) ∧
    (∀ σ : LiveState, Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalClusterMass p σ) /
        Real.log ((rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source (rule.generation n).network.target))
      atTop (𝓝 (Real.log ((spectralRadius ℂ
        ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)))) ∧
    Tendsto (rule.pivotalLogarithmicGrowth p) atTop
      (𝓝 (Real.log (deriv rule.network.reliability p) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) := by
  obtain ⟨hconnected, hcut, hderivative⟩ :=
    rule.interior_fixed_point_geometry p hp hp' hfixed hscale
  exact ⟨rule.finite_edge_growth_formula hconnected,
    rule.finite_cluster_mass_dimension p hfixed hp hp' hsymmetric hconnected hscale hcut,
    (rule.pivotal_dimension p hfixed hconnected hderivative hscale).2.2⟩

theorem interior_fixed_point_spectral_dominance (rule : Rule) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (hsymmetric : rule.TerminalSymmetric)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    0 < deriv rule.network.reliability p ∧
    deriv rule.network.reliability p <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ∧
    |secondaryRoot (massPlaneBlock (rule.network.massMatrix p))| <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal := by
  obtain ⟨hconnected, hcut, hderivative⟩ :=
    rule.interior_fixed_point_geometry p hp hp' hfixed hscale
  obtain ⟨symmetry, hs, ht⟩ := hsymmetric
  exact ⟨hderivative, rule.network.mass_spectral_dominance p hfixed hp hp'
    symmetry hs ht hconnected hscale hcut⟩

end
end Universality.Rule

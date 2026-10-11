import Universality.Percolation.FiniteCore
import Universality.Graph.SubstitutionConnectivity

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

/-- The manuscript's finite classical rule conditions. The edge-cut condition
is expressed as survival of every one-edge deletion, equivalent to terminal
edge connectivity at least two for a connected graph. Loops are already
excluded by `FiniteNetwork`. No infinite limit is part of this definition. -/
structure Classical (rule : Rule) : Prop where
  connected : ∀ vertex, rule.network.fullGraph.Reachable rule.network.source vertex
  simple : Function.Injective (fun edge =>
    s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2))
  canonical : ∀ edge, ∃ walk : rule.network.fullGraph.Walk rule.network.source rule.network.target,
    walk.IsPath ∧ s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) ∈ walk.edges
  scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target
  cut : ∀ edge, rule.network.crosses (onlyClosed edge) = true
  symmetric : ∃ symmetry : rule.network.NetworkSymmetry,
    Function.Involutive symmetry.vertex ∧
      symmetry.vertex rule.network.source = rule.network.target

theorem Classical.massAdmissible {rule : Rule} (h : rule.Classical) : rule.MassAdmissible := by
  obtain ⟨symmetry, hinvolutive, hsource⟩ := h.symmetric
  have htarget : symmetry.vertex rule.network.target = rule.network.source := by
    rw [← hsource]
    exact hinvolutive _
  exact ⟨h.connected _, h.scale, h.cut, ⟨symmetry, hsource, htarget⟩⟩

theorem Classical.exists_interior_fixed_point {rule : Rule} (h : rule.Classical) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ rule.network.reliability p = p :=
  rule.network.exists_interior_fixed_point (h.connected _) h.scale h.cut

/-- The mass formula for each interior fixed point of a classical finite rule.
The threshold-identification and uniqueness theorems remain separate. -/
theorem Classical.mass_dimension {rule : Rule} (h : rule.Classical) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) (σ : LiveState) :
    Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalClusterMass p σ) /
        Real.log ((rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source (rule.generation n).network.target))
      atTop (𝓝 (Real.log ((spectralRadius ℂ
        ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) :=
  rule.finite_cluster_mass_dimension p hfixed hp hp' h.massAdmissible.symmetric
    (h.connected _) h.scale h.cut σ

theorem Classical.pivotal_dimension {rule : Rule} (h : rule.Classical) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    Tendsto (rule.pivotalLogarithmicGrowth p) atTop
      (𝓝 (Real.log (deriv rule.network.reliability p) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) :=
  (rule.pivotal_dimension p hfixed (h.connected _)
    (rule.network.reliability_derivative_pos hp hp' (h.connected _)) h.scale).2.2

end
end Universality.Rule

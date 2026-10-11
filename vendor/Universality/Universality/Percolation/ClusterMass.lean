import Universality.Graph.Iteration
import Universality.Percolation.FirstMoments
import Universality.Percolation.LocalMassResponse
import Universality.Matrix.ColumnGrowth

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- The actual number of open edges in the active root cluster (or the union
of the two terminal clusters in state `both`). -/
def clusterEdgeCount (σ : LiveState) (ω : Configuration edges) : ℕ :=
  (Finset.univ.filter fun edge : Fin edges =>
    ω edge = true ∧ R.active σ ω (R.endpoint edge).1 = true).card

theorem childState_connected_iff (σ : LiveState) (ω : Configuration edges)
    (edge : Fin edges) :
    R.childState σ ω edge = some .connected ↔
      ω edge = true ∧ R.active σ ω (R.endpoint edge).1 = true := by
  by_cases hopen : ω edge = true
  · have hactive := R.active_endpoints_eq_of_open σ ω edge hopen
    simp only [childState, hopen, ← hactive]
    cases R.active σ ω (R.endpoint edge).1 <;> simp
  · have hclosed : ω edge = false := Bool.eq_false_iff.mpr hopen
    simp only [childState, hclosed]
    cases R.active σ ω (R.endpoint edge).1 <;>
      cases R.active σ ω (R.endpoint edge).2 <;> simp

theorem clusterEdgeCount_eq_liveCount (σ : LiveState) (ω : Configuration edges) :
    R.clusterEdgeCount σ ω = R.liveCount σ .connected ω := by
  unfold clusterEdgeCount liveCount
  congr 1
  ext edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    R.childState_connected_iff]

def conditionalClusterMass (p : ℝ) (σ : LiveState) : ℝ :=
  (∑ ω : Configuration edges, if R.conditioning σ ω then
    bernoulliWeight p ω * R.clusterEdgeCount σ ω else 0) /
      R.conditioningProbability p σ

theorem conditionalClusterMass_eq (p : ℝ) (σ : LiveState) :
    R.conditionalClusterMass p σ = R.massMatrix p σ .connected := by
  simp only [conditionalClusterMass, massMatrix, clusterEdgeCount_eq_liveCount]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

theorem generation_conditionalClusterMass (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hp : 0 < p) (hp' : p < 1)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source) (n : ℕ) (σ : LiveState) :
    (rule.generation n).network.conditionalClusterMass p σ =
      (rule.network.massMatrix p ^ (n + 1)) σ .connected := by
  rw [FiniteNetwork.conditionalClusterMass_eq,
    rule.generation_massMatrix p hfixed hp hp' symmetry hs ht]

/-- A finite-graph annealed mass-dimension theorem. Positivity of the connected
column and a positive eigenvector are explicit hypotheses; no infinite-volume
cluster limit or almost-sure dimension is asserted here. -/
theorem conditional_cluster_mass_dimension (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hp : 0 < p) (hp' : p < 1)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (reachable : rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (weight : LiveState → ℝ) (radius : ℝ)
    (hw : ∀ σ, 0 < weight σ) (hr : 0 < radius)
    (heigen : rule.network.massMatrix p *ᵥ weight = radius • weight)
    (hcolumn : ∀ σ, 0 < rule.network.massMatrix p σ .connected) (σ : LiveState) :
    Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalClusterMass p σ) /
        Real.log ((rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source (rule.generation n).network.target))
      atTop (𝓝 (Real.log radius /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) := by
  have h := matrix_entry_dimension (rule.network.massMatrix p) weight radius
    (rule.network.fullGraph.dist rule.network.source rule.network.target)
    (rule.network.massMatrix_nonneg hp.le hp'.le) hw hr heigen σ .connected hcolumn
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, generation_conditionalClusterMass rule p hfixed hp hp' symmetry hs ht,
    generation_terminal_distance rule reachable, Nat.cast_pow] using hshift

end
end Universality.Rule

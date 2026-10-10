import Universality.Percolation.GeometricMassPositivity
import Universality.Graph.TerminalSymmetricRule

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem exists_source_incident_edge
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    ∃ edge, (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source := by
  obtain ⟨walk⟩ := hconnected
  have hexists {u v : Fin vertices} (walk : R.fullGraph.Walk u v) (hne : u ≠ v) :
      ∃ edge, (R.endpoint edge).1 = u ∨ (R.endpoint edge).2 = u := by
    cases walk with
    | nil => exact (hne rfl).elim
    | cons hadj tail =>
      obtain ⟨_, edge, _, h | h⟩ := hadj
      · exact ⟨edge, Or.inl (congrArg Prod.fst h)⟩
      · exact ⟨edge, Or.inr (congrArg Prod.snd h)⟩
  exact hexists walk R.terminals_distinct

theorem incident_endpoints_ne_target (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    (R.endpoint edge).1 ≠ R.target ∧ (R.endpoint edge).2 ≠ R.target := by
  have hnotadj : ¬ R.fullGraph.Adj R.source R.target := by
    intro h
    have hd := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  rcases hincident with hsource | hsource
  · constructor
    · simpa only [hsource] using R.terminals_distinct
    · intro htarget
      apply hnotadj
      exact ⟨R.terminals_distinct, edge, rfl,
        Or.inl (Prod.ext hsource htarget)⟩
  · constructor
    · intro htarget
      apply hnotadj
      exact ⟨R.terminals_distinct, edge, rfl,
        Or.inr (Prod.ext htarget hsource)⟩
    · simpa only [hsource] using R.terminals_distinct

theorem massPlaneBlock_pos_of_geometry {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) :
    (∀ i j, 0 < massPlaneBlock (R.massMatrix p) i j) ∧
      (∀ σ, 0 < R.massMatrix p σ .connected) := by
  obtain ⟨edge, hincident⟩ := R.exists_source_incident_edge hconnected
  obtain ⟨hfirst, hsecond⟩ := R.incident_endpoints_ne_target edge hincident hscale
  exact ⟨R.massPlaneBlock_pos_of_edge hp hp' edge hincident hfirst hsecond (hcut edge),
    R.massMatrix_connected_column_pos_of_edge hp hp' edge hincident hfirst hsecond
      ((R.crosses_eq_true _).mpr hconnected)⟩

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

/-- The expected open-cluster mass dimension on actual finite iterates.
The geometric hypotheses are terminal distance at least two and survival of
every single-edge deletion. The parameter is an interior reliability fixed point. -/
theorem finite_cluster_mass_dimension (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hp : 0 < p) (hp' : p < 1)
    (hsymmetric : rule.TerminalSymmetric)
    (hconnected : rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    (hcut : ∀ edge, rule.network.crosses (onlyClosed edge) = true) (σ : LiveState) :
    Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalClusterMass p σ) /
        Real.log ((rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source (rule.generation n).network.target))
      atTop (𝓝 (Real.log ((spectralRadius ℂ
        ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) := by
  obtain ⟨symmetry, hs, ht⟩ := hsymmetric
  obtain ⟨hblock, hcolumn⟩ := rule.network.massPlaneBlock_pos_of_geometry hp hp'
    hconnected hscale hcut
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  apply rule.conditional_cluster_mass_dimension p hfixed hp hp' symmetry hs ht hconnected
    (massPlaneLift ![massPlaneBlock (rule.network.massMatrix p) 0 1,
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
        massPlaneBlock (rule.network.massMatrix p) 0 0])
  · apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  · exact positiveRoot_pos _ hblock
  · rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul]
  · exact hcolumn

end
end Universality.Rule

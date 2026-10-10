import Universality.Percolation.VertexMomentRecursion
import Universality.Percolation.VertexMassGrowth
import Universality.Probability.BranchingMomentGrowth

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix
set_option maxHeartbeats 0

/-- All integer moments of the actual conditional internal-vertex mass grow
at most as the corresponding power of the genuine critical spectral radius. -/
theorem Classical.internal_vertex_moment_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∀ r : ℕ, ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (rule.generation n).network.conditionalVertexMoment p state r ≤
        bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (r * n) := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp' (h.connected _) h.scale h.cut).1
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  have hradius : 1 < positiveRoot (massPlaneBlock (rule.network.massMatrix p)) :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.network.pivotal_response_lt_mass_root p hfixed hp hp' hblock)
  have hspectral : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal =
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) := by
    rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
      ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  rw [hspectral]
  refine branching_all_moment_bounds
    (fun state => rule.network.conditionalCellWeight p (state == .connected))
    (fun state configuration => (rule.network.internalSelectedMass true (state == .both) configuration : ℝ))
    rule.network.childState (rule.network.massMatrix p)
    (massPlaneLift ![massPlaneBlock (rule.network.massMatrix p) 0 1,
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) - massPlaneBlock (rule.network.massMatrix p) 0 0])
    (positiveRoot (massPlaneBlock (rule.network.massMatrix p)))
    (rule.network.massMatrix_nonneg hp.le hp'.le) ?_ hradius ?_ ?_ ?_ ?_
    (fun n state r => (rule.generation n).network.conditionalVertexMoment p state r) ?_ ?_ ?_ ?_
  · apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  · rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul]
  · intro state configuration
    exact rule.network.conditionalCellWeight_nonneg hp.le hp'.le _ _
  · intro state configuration
    exact Nat.cast_nonneg _
  · intro values state
    rw [rule.network.massMatrix_mulVec_response, rule.network.conditionalResponse_eq_weighted]
    apply Finset.sum_congr rfl
    intro configuration _
    congr 1
    unfold liveResponse
    apply Finset.sum_congr rfl
    intro child _
    cases rule.network.childState state configuration child <;> rfl
  · intro n state r
    exact (rule.generation n).network.conditionalInternalMoment_nonneg p hp.le hp'.le _ _ _ r
  · intro n state
    exact (rule.generation n).network.conditionalInternalMoment_zero p
      (by rwa [rule.generation_fixed_point p hfixed n])
      (by rwa [rule.generation_fixed_point p hfixed n]) _ _ _
  · obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := h.internal_vertex_mass_bounds p hp hp' hfixed
    refine ⟨upper, hupper, ?_⟩
    intro n state
    rw [conditionalVertexMoment_one, ← hspectral]
    exact (hbounds n state).2
  · exact rule.generation_conditionalVertexMoment h.massAdmissible.symmetric p hp hp' hfixed

end
end Universality.Rule

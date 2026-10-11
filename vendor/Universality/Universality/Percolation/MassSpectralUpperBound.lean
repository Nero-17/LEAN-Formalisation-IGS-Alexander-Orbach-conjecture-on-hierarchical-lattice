import Universality.Percolation.MassRowBounds
import Universality.Matrix.StrictRowBound
import Universality.Graph.ClassicalRule

namespace Universality.FiniteNetwork
noncomputable section
open Matrix

theorem mass_spectralRadius_lt_edges {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true)
    (symmetry : R.NetworkSymmetry) (hs : symmetry.vertex R.source = R.target)
    (ht : symmetry.vertex R.target = R.source) :
    (spectralRadius ℂ ((R.massMatrix p).map Complex.ofReal)).toReal < (edges : ℝ) := by
  have hblock := (R.massPlaneBlock_pos_of_geometry hp hp' hconnected hscale hcut).1
  have hplane := R.massMatrix_preservesMassPlane p symmetry hs ht
  have hweight : ∀ state, 0 < massPlaneLift
      ![massPlaneBlock (R.massMatrix p) 0 1,
        positiveRoot (massPlaneBlock (R.massMatrix p)) - massPlaneBlock (R.massMatrix p) 0 0] state := by
    apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  rw [massPlane_spectralRadius _ (R.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  exact positive_eigenvalue_lt_of_strict_row_bound (R.massMatrix p)
    (massPlaneLift ![massPlaneBlock (R.massMatrix p) 0 1,
      positiveRoot (massPlaneBlock (R.massMatrix p)) - massPlaneBlock (R.massMatrix p) 0 0])
    (positiveRoot (massPlaneBlock (R.massMatrix p))) (edges : ℝ)
    (R.massMatrix_nonneg hp.le hp'.le) hweight (positiveRoot_pos _ hblock).le (Nat.cast_nonneg _)
    (by rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul])
    (R.massMatrix_row_sum_le_edges p hp hp' hconnected) .single
    (R.massMatrix_single_row_sum_lt_edges p hp hp' hconnected hscale) 4
    (R.massMatrix_fourth_power_pos p hp hp' hconnected hscale hcut)

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem Classical.mass_spectralRadius_lt_edges {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal < (rule.edges : ℝ) := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  exact rule.network.mass_spectralRadius_lt_edges p hp hp' (h.connected _) h.scale h.cut symmetry hs ht

end
end Universality.Rule

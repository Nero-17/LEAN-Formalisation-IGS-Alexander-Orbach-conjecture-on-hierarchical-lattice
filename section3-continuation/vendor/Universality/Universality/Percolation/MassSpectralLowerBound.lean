import Universality.Graph.IncidentDegree
import Universality.Matrix.StrictRowLowerBound
import Universality.Percolation.MassSpectralUpperBound

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix

theorem Classical.terminal_degree_lt_mass_spectralRadius {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    (rule.network.fullGraph.degree rule.network.source : ℝ) <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp' (h.connected _) h.scale h.cut).1
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  have hweight : ∀ state, 0 < massPlaneLift
      ![massPlaneBlock (rule.network.massMatrix p) 0 1,
        positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          massPlaneBlock (rule.network.massMatrix p) 0 0] state := by
    apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple,
    massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  exact strict_row_lower_bound_lt_positive_eigenvalue (rule.network.massMatrix p)
    (massPlaneLift ![massPlaneBlock (rule.network.massMatrix p) 0 1,
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) - massPlaneBlock (rule.network.massMatrix p) 0 0])
    (positiveRoot (massPlaneBlock (rule.network.massMatrix p))) (rule.network.sourceIncidentEdges.card : ℝ)
    (rule.network.massMatrix_nonneg hp.le hp'.le) hweight (positiveRoot_pos _ hblock).le (Nat.cast_nonneg _)
    (by rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul])
    (rule.network.massMatrix_row_sum_ge_incident p hp hp' (h.connected _)) .connected
    (rule.network.massMatrix_connected_row_sum_gt_incident p hp hp' h.connected h.scale) 4
    (rule.network.massMatrix_fourth_power_pos p hp hp' (h.connected _) h.scale h.cut)

theorem Classical.terminal_degree_spectral_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    2 ≤ rule.network.fullGraph.degree rule.network.source ∧
      (rule.network.fullGraph.degree rule.network.source : ℝ) <
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ∧
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal < (rule.edges : ℝ) := by
  refine ⟨?_, h.terminal_degree_lt_mass_spectralRadius p hp hp', h.mass_spectralRadius_lt_edges p hp hp'⟩
  rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
  exact rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut

end
end Universality.Rule

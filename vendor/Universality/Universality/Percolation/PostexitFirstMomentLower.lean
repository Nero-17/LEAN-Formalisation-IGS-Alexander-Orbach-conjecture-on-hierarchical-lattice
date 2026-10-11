import Universality.Percolation.GenerationFirstMomentRecursion
import Universality.Analysis.AffinePopulationLowerComparison
import Universality.Percolation.MassRowLowerBounds
import Universality.Percolation.SubcriticalBoundaryMeanLimit
import Universality.Percolation.RenormalisationLimits

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0

theorem Classical.postexit_vertex_mass_lower_comparison {rule : Rule} (h : rule.Classical)
    (p exitParameter : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hexit : 0 < exitParameter) (hexit' : exitParameter < 1)
    (offset : ℕ) (hparameter : rule.network.reliability^[offset] p = exitParameter)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hbase : ∀ state, scale * (rule.network.conditionalVertexMass exitParameter state + rule.vertices) ≤
      (rule.generation offset).network.conditionalVertexMass p state) :
    ∀ n state, scale * ((rule.generation n).network.conditionalVertexMass exitParameter state + rule.vertices) ≤
      (rule.generation (offset + n)).network.conditionalVertexMass p state := by
  have hcrossing (n : ℕ) : (rule.generation (offset + n)).network.reliability p =
      (rule.generation n).network.reliability exitParameter := by
    rw [rule.generation_reliability_iterate, rule.generation_reliability_iterate, ← hparameter,
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hpositive (n : ℕ) := ((rule.generation n).network.reliability_pos_iff_connected hexit hexit').mpr
    ((h.generation n).connected _)
  have hless (n : ℕ) := (rule.generation n).network.reliability_lt_one hexit hexit'
  apply affine_population_lower_comparison
    (fun n state child => rule.network.massMatrix ((rule.generation n).network.reliability exitParameter) state child)
    (fun n state => rule.network.conditionalVertexMass ((rule.generation n).network.reliability exitParameter) state)
    (fun n state => (rule.generation n).network.conditionalVertexMass exitParameter state)
    (fun n state => (rule.generation (offset + n)).network.conditionalVertexMass p state)
    (rule.vertices : ℝ) scale (Nat.cast_nonneg _) hscale
  · intro n state child
    exact rule.network.massMatrix_nonneg (hpositive n).le (hless n).le state child
  · intro n state
    have hdegree : (2 : ℝ) ≤ rule.network.sourceIncidentEdges.card := by
      exact_mod_cast rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact hdegree.trans (rule.network.massMatrix_row_sum_ge_incident _ (hpositive n) (hless n) (h.connected _) state)
  · intro n state
    exact ⟨rule.network.conditionalInternalMean_nonneg _ (hpositive n).le (hless n).le _ _ _,
      rule.network.conditionalVertexMass_le_vertices (hpositive n).le (hless n).le
        ((rule.network.reliability_pos_iff_connected (hpositive n) (hless n)).mpr (h.connected _))
        (rule.network.reliability_lt_one (hpositive n) (hless n)) state⟩
  · intro n state
    exact h.generation_conditionalVertexMass_offcritical exitParameter hexit hexit' n state
  · intro n state
    rw [← Nat.add_assoc, h.generation_conditionalVertexMass_offcritical p hp hp', hcrossing]
  · intro state
    rw [Nat.add_zero, show rule.generation 0 = rule from rfl]
    exact hbase state

end
end Universality.Rule

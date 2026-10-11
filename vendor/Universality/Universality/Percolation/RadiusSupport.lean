import Universality.Percolation.RadiusBirthSeries
import Universality.Graph.GenerationDiameter

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem clusterRadiusRootCount_eq_zero_of_diameter_bound (R : FiniteNetwork vertices edges)
    (bound : ℕ) (hbound : ∀ u v, R.fullGraph.dist u v ≤ bound)
    (cluster : Finset (Fin vertices)) (radius : ℕ) (hradius : bound < radius) :
    R.clusterRadiusRootCount cluster radius = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro root hroot
  have hrad := (Finset.mem_filter.mp hroot).2
  have hle : R.clusterRadius cluster root ≤ bound :=
    Finset.sup_le (fun vertex _ => hbound root vertex)
  omega

theorem expectedInternalRadiusRootCount_eq_zero_of_diameter_bound (R : FiniteNetwork vertices edges)
    (bound : ℕ) (hbound : ∀ u v, R.fullGraph.dist u v ≤ bound)
    (p : ℝ) (radius : ℕ) (hradius : bound < radius) :
    R.expectedInternalRadiusRootCount p radius = 0 := by
  simp only [expectedInternalRadiusRootCount, internalRadiusRootCount,
    R.clusterRadiusRootCount_eq_zero_of_diameter_bound bound hbound _ radius hradius,
    Finset.sum_const_zero, Nat.cast_zero, mul_zero]

theorem expectedBirthRadiusRootCount_eq_zero_of_diameter_bound
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (bound : ℕ) (hbound : ∀ u v, (R.substitute S).fullGraph.dist u v ≤ bound)
    (p : ℝ) (radius : ℕ) (hradius : bound < radius) :
    R.expectedBirthRadiusRootCount S p radius = 0 := by
  simp only [expectedBirthRadiusRootCount, birthRadiusRootCount,
    (R.substitute S).clusterRadiusRootCount_eq_zero_of_diameter_bound bound hbound _ radius hradius,
    Finset.sum_const_zero, Nat.cast_zero, mul_zero]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

theorem Classical.radius_birth_support {rule : Rule} (h : rule.Classical) :
    ∃ bound : ℕ, 0 < bound ∧ ∀ n p radius,
      bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n < radius →
        rule.expectedRadiusBirth p radius n = 0 := by
  obtain ⟨bound, hpositive, hdiameter⟩ := h.generation_diameter_bound
  refine ⟨bound, hpositive, ?_⟩
  intro n p radius hradius
  cases n with
  | zero =>
    exact rule.network.expectedInternalRadiusRootCount_eq_zero_of_diameter_bound
      _ (hdiameter 0) p radius hradius
  | succ n =>
    apply rule.network.expectedBirthRadiusRootCount_eq_zero_of_diameter_bound
      (rule.generation n).network _ _ p radius hradius
    intro u v
    obtain ⟨u, rfl⟩ := (rule.generationTopDecomposition n).vertex.surjective u
    obtain ⟨v, rfl⟩ := (rule.generationTopDecomposition n).vertex.surjective v
    have hdistance : (rule.network.substitute (rule.generation n).network).fullGraph.dist
        ((rule.generationTopDecomposition n).vertex u) ((rule.generationTopDecomposition n).vertex v) =
        (rule.generation (n + 1)).network.fullGraph.dist u v :=
      graph_iso_distance_of_reachable ((rule.generationTopDecomposition n).openGraphIso (fun _ => true))
        (((h.generation (n + 1)).connected u).symm.trans ((h.generation (n + 1)).connected v))
    rw [hdistance]
    exact hdiameter (n + 1) u v

end
end Universality.Rule

import IGSIII.Geometry.ActualChemicalSkeleton
import Mathlib.Topology.MetricSpace.GromovHausdorff

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

/-- The actual entire finite retained cluster, with its normalized chemical
graph distance. The phantom scale index fixes the metric unambiguously. -/
def ActualFiniteCluster (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (_scale : ℝ) (_scale_positive : 0 < _scale) (depth : ℕ) : Type :=
  RetainedSkeletonVertex (rule.generation depth).network (configuration depth)

instance actualFiniteClusterMetricSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scale_positive : 0 < scale) (depth : ℕ) :
    MetricSpace (ActualFiniteCluster rule configuration scale scale_positive depth) where
  dist first last := (((rule.generation depth).network.openGraph (configuration depth)).dist first.val last.val : ℝ) / scale ^ (depth + 1)
  dist_self first := by simp
  dist_comm first last := by simp only [SimpleGraph.dist_comm]
  dist_triangle first middle last := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (pow_pos scale_positive _).le
    exact_mod_cast (first.property.symm.trans middle.property).dist_triangle_left last.val
  eq_of_dist_eq_zero := by
    intro first last distance_zero
    have numerator_zero := (div_eq_zero_iff.mp distance_zero).resolve_right (pow_pos scale_positive _).ne'
    have graph_distance_zero : ((rule.generation depth).network.openGraph (configuration depth)).dist first.val last.val = 0 := by
      exact_mod_cast numerator_zero
    exact Subtype.ext ((first.property.symm.trans last.property).dist_eq_zero_iff.mp graph_distance_zero)

instance actualFiniteClusterFinite (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scale_positive : 0 < scale) (depth : ℕ) :
    Finite (ActualFiniteCluster rule configuration scale scale_positive depth) :=
  inferInstanceAs (Finite (RetainedSkeletonVertex (rule.generation depth).network (configuration depth)))

instance actualFiniteClusterCompactSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scale_positive : 0 < scale) (depth : ℕ) :
    CompactSpace (ActualFiniteCluster rule configuration scale scale_positive depth) := inferInstance

instance actualFiniteClusterNonempty (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scale_positive : 0 < scale) (depth : ℕ) :
    Nonempty (ActualFiniteCluster rule configuration scale scale_positive depth) :=
  ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩

def retainedFiniteVertexEmbedding (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale) (age depth : ℕ) (bound : age ≤ depth) :
    RetainedSkeletonVertex (rule.generation age).network (configuration age) ↪
      ActualFiniteCluster rule configuration scale scale_positive depth :=
  retainedPersistentVertexEmbedding rule configuration coherent age depth bound

theorem retainedFiniteVertexEmbedding_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scale_positive : 0 < scale) (age depth : ℕ) (bound : age ≤ depth)
    (vertex : RetainedSkeletonVertex (rule.generation age).network (configuration age)) :
    (retainedFiniteVertexEmbedding rule configuration coherent scale scale_positive age depth bound vertex).val =
      persistentVertexEmbedding rule age depth bound vertex.val := rfl

end
end IGSIII.Geometry

import IGSIII.Geometry.RootedComponentPersistence
import Mathlib.Topology.MetricSpace.GromovHausdorff

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- The actual finite planted component with its intrinsic graph distance in
root units. The other side of a noncrossing socket is never joined internally. -/
def RootedFiniteComponent (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool)
    (_scale : ℝ) (_scalePositive : 0 < _scale) (_offset depth : ℕ) : Type :=
  RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide

instance rootedFiniteComponentMetricSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool)
    (scale : ℝ) (scalePositive : 0 < scale) (offset depth : ℕ) :
    MetricSpace (RootedFiniteComponent rule configuration sourceSide scale scalePositive offset depth) where
  dist first last := (((rule.generation depth).network.openGraph (configuration depth)).dist first.val last.val : ℝ) / scale ^ (depth + 1 + offset)
  dist_self first := by simp
  dist_comm first last := by simp only [SimpleGraph.dist_comm]
  dist_triangle first middle last := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (pow_pos scalePositive _).le
    exact_mod_cast (first.property.symm.trans middle.property).dist_triangle_left last.val
  eq_of_dist_eq_zero := by
    intro first last zeroDistance
    have numeratorZero := (div_eq_zero_iff.mp zeroDistance).resolve_right (pow_pos scalePositive _).ne'
    have graphZero : ((rule.generation depth).network.openGraph (configuration depth)).dist first.val last.val = 0 := by
      exact_mod_cast numeratorZero
    exact Subtype.ext ((first.property.symm.trans last.property).dist_eq_zero_iff.mp graphZero)

instance rootedFiniteComponentFinite (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool)
    (scale : ℝ) (scalePositive : 0 < scale) (offset depth : ℕ) :
    Finite (RootedFiniteComponent rule configuration sourceSide scale scalePositive offset depth) :=
  inferInstanceAs (Finite (RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide))

instance rootedFiniteComponentCompactSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool)
    (scale : ℝ) (scalePositive : 0 < scale) (offset depth : ℕ) :
    CompactSpace (RootedFiniteComponent rule configuration sourceSide scale scalePositive offset depth) := inferInstance

instance rootedFiniteComponentNonempty (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (sourceSide : Bool)
    (scale : ℝ) (scalePositive : 0 < scale) (offset depth : ℕ) :
    Nonempty (RootedFiniteComponent rule configuration sourceSide scale scalePositive offset depth) :=
  ⟨⟨plantedVertex (rule.generation depth).network sourceSide, SimpleGraph.Reachable.refl _⟩⟩

def rootedFiniteVertexEmbedding (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (scale : ℝ) (scalePositive : 0 < scale) (offset age depth : ℕ) (bound : age ≤ depth) :
    RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide ↪
      RootedFiniteComponent rule configuration sourceSide scale scalePositive offset depth :=
  retainedComponentPersistentEmbedding rule configuration coherent sourceSide age depth bound

@[simp] theorem rootedFiniteVertexEmbedding_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (scale : ℝ) (scalePositive : 0 < scale) (offset age depth : ℕ) (bound : age ≤ depth)
    (vertex : RetainedComponentVertex (rule.generation age).network (configuration age) sourceSide) :
    (rootedFiniteVertexEmbedding rule configuration coherent sourceSide scale scalePositive offset age depth bound vertex).val =
      persistentVertexEmbedding rule age depth bound vertex.val := rfl

end
end IGSIII.Geometry

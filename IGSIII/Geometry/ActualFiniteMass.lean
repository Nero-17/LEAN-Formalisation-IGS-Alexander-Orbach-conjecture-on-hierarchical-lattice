import IGSIII.Geometry.ActualFiniteCluster
import IGSIII.Geometry.BoxDimensionPopulation
import IGSIII.Chemical.SmallBall.ComponentVertexOwnership
import Mathlib.Probability.UniformOn

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory ProbabilityTheory

instance actualFiniteClusterFintype (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    Fintype (ActualFiniteCluster rule configuration scale scalePositive depth) := Fintype.ofFinite _

instance actualFiniteClusterMeasurableSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    MeasurableSpace (ActualFiniteCluster rule configuration scale scalePositive depth) := ⊤

instance actualFiniteClusterBorelSpace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    BorelSpace (ActualFiniteCluster rule configuration scale scalePositive depth) :=
  ⟨borel_eq_top_of_countable.symm⟩

/-- Uniform counting probability on every vertex of the actual retained
finite cluster, including both persistent terminals. -/
def actualFiniteClusterMeasure (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    Measure (ActualFiniteCluster rule configuration scale scalePositive depth) := uniformOn Set.univ

instance actualFiniteClusterMeasure_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    IsProbabilityMeasure (actualFiniteClusterMeasure rule configuration scale scalePositive depth) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set (ActualFiniteCluster rule configuration scale scalePositive depth))))

def selectedRootInteriorEmbedding (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    SelectedComponentInterior rule marks depth [] .connected ↪
      ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth where
  toFun point := ⟨point.val.val,
    (single_oriented_component_selected_iff (rule.generation depth).network _ .connected
      (by decide) (by decide) (markedGenerationConfiguration_crosses rule marks crossing depth [] true) _).mp point.property⟩
  inj' := by
    intro first last equality
    have raw : first.val.val = last.val.val := congrArg
      (fun point : ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        scale scalePositive depth => point.val) equality
    exact Subtype.ext (Subtype.ext raw)

theorem actualFiniteCluster_card (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    (Nat.card (ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive depth) : ℝ) = markedComponentVertexMass rule marks depth [] + 2 := by
  rw [ActualFiniteCluster, retainedSkeletonVertex_card_connected _ _
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true), Nat.cast_add, Nat.cast_ofNat]
  rfl

end
end IGSIII.Geometry

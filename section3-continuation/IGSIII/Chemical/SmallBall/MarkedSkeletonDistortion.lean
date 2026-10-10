import IGSIII.Chemical.SmallBall.ActualChemicalTerminals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution IGSIII.Geometry Filter
open scoped ENNReal Topology

noncomputable section

noncomputable def anchorRetraction {Index Source : Type*} (embedding : Index ↪ Source)
    (projection : Source → Index) (point : Source) : Index := by
  classical
  exact if membership : ∃ anchor, embedding anchor = point then Classical.choose membership else projection point

theorem anchorRetraction_embedding {Index Source : Type*} (embedding : Index ↪ Source)
    (projection : Source → Index) (anchor : Index) :
    anchorRetraction embedding projection (embedding anchor) = anchor := by
  classical
  unfold anchorRetraction
  rw [dif_pos ⟨anchor, rfl⟩]
  apply embedding.injective
  exact Classical.choose_spec (show ∃ other, embedding other = embedding anchor from ⟨anchor, rfl⟩)

theorem anchorRetraction_preserves_mesh {Index Source : Type*} [PseudoMetricSpace Source]
    (embedding : Index ↪ Source) (projection : Source → Index) {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (bounds : ∀ point, dist point (embedding (projection point)) ≤ radius) (point : Source) :
    dist point (embedding (anchorRetraction embedding projection point)) ≤ radius := by
  classical
  by_cases membership : ∃ anchor, embedding anchor = point
  · unfold anchorRetraction
    rw [dif_pos membership, Classical.choose_spec membership, dist_self]
    exact radiusNonnegative
  · simpa only [anchorRetraction, dif_neg membership] using bounds point

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (limitLength : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (lengthNonnegative : ∀ depth edge, 0 ≤ limitLength depth edge)
variable (lengthPositive : ∀ depth edge, configuration depth edge = true → 0 < limitLength depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limitLength coarse edge)))

theorem actualFiniteCluster_marked_skeleton_distortion (age : ℕ) {epsilon : ℝ} (epsilonPositive : 0 < epsilon) :
    ∀ᶠ depth : ℕ in atTop, ∃ bound : age ≤ depth,
      (∀ first last : RetainedSkeletonVertex (rule.generation age).network (configuration age),
        |dist (retainedFiniteVertexEmbedding rule configuration coherent scale scalePositive age depth bound first)
            (retainedFiniteVertexEmbedding rule configuration coherent scale scalePositive age depth bound last) -
          dist (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
              childConvergence age first)
            (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
              childConvergence age last)| < epsilon) ∧
      (∀ sourceSide : Bool, retainedFiniteVertexEmbedding rule configuration coherent scale scalePositive age depth bound
          (retainedTerminalVertex rule configuration crossing age sourceSide) =
        actualFiniteClusterTerminal rule configuration crossing scale scalePositive depth sourceSide) ∧
      (∀ sourceSide : Bool, actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative
          lengthPositive childConvergence age (retainedTerminalVertex rule configuration crossing age sourceSide) =
        actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
          childConvergence sourceSide) := by
  have uniform : ∀ᶠ depth in atTop, ∀ first last : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      |persistentNormalizedDistance rule configuration scale age first.val last.val depth -
        dist (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
            childConvergence age first)
          (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
            childConvergence age last)| < epsilon := by
    apply Filter.eventually_all.mpr
    intro first
    apply Filter.eventually_all.mpr
    intro last
    have convergence := actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive
      age (limitLength age) (childConvergence age) (first.property.symm.trans last.property)
    rw [← actualChemicalVertex_distance rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative
      lengthPositive childConvergence age first last] at convergence
    exact (Metric.tendsto_nhds.mp convergence epsilon epsilonPositive).mono (fun _ close => by simpa only [Real.dist_eq] using close)
  filter_upwards [eventually_ge_atTop age, uniform] with depth bound close
  refine ⟨bound, ?_, ?_, ?_⟩
  · intro first last
    have comparison := close first last
    change |((((rule.generation depth).network.openGraph (configuration depth)).dist
        (persistentVertexEmbedding rule age depth bound first.val) (persistentVertexEmbedding rule age depth bound last.val) : ℝ) /
      scale ^ (depth + 1)) - dist
        (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
          childConvergence age first)
        (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
          childConvergence age last)| < epsilon
    simpa only [persistentNormalizedDistance, dif_pos bound] using comparison
  · exact retainedFiniteVertexEmbedding_terminal rule configuration coherent crossing scale scalePositive age depth bound
  · intro sourceSide
    exact (actualChemicalTerminal_eq_vertex rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative
      lengthPositive childConvergence age sourceSide).symm

theorem actualFiniteCluster_terminal_projection_identity (age depth : ℕ) (bound : age ≤ depth)
    (projection : ActualFiniteCluster rule configuration scale scalePositive depth →
      RetainedSkeletonVertex (rule.generation age).network (configuration age)) (sourceSide : Bool) :
    actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence
      age (anchorRetraction (retainedFiniteVertexEmbedding rule configuration coherent scale scalePositive age depth bound) projection
        (actualFiniteClusterTerminal rule configuration crossing scale scalePositive depth sourceSide)) =
      actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
        childConvergence sourceSide := by
  rw [← retainedFiniteVertexEmbedding_terminal rule configuration coherent crossing scale scalePositive age depth bound sourceSide,
    anchorRetraction_embedding]
  exact (actualChemicalTerminal_eq_vertex rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative
    lengthPositive childConvergence age sourceSide).symm

theorem actualFiniteCluster_terminal_projection_distance_zero (age depth : ℕ) (bound : age ≤ depth)
    (projection : ActualFiniteCluster rule configuration scale scalePositive depth →
      RetainedSkeletonVertex (rule.generation age).network (configuration age)) (sourceSide : Bool) :
    dist (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence
      age (anchorRetraction (retainedFiniteVertexEmbedding rule configuration coherent scale scalePositive age depth bound) projection
        (actualFiniteClusterTerminal rule configuration crossing scale scalePositive depth sourceSide)))
      (actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
        childConvergence sourceSide) = 0 := by
  rw [actualFiniteCluster_terminal_projection_identity, dist_self]

end
end IGSIII.Chemical.SmallBall
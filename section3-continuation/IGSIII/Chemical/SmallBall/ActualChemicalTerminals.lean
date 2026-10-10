import IGSIII.Geometry.CriticalChemicalGH

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution IGSIII.Geometry Filter
open scoped ENNReal Topology

noncomputable section

def retainedTerminalVertex (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (depth : ℕ) (sourceSide : Bool) : RetainedSkeletonVertex (rule.generation depth).network (configuration depth) :=
  ⟨plantedVertex (rule.generation depth).network sourceSide, by
    cases sourceSide with
    | false => exact ((rule.generation depth).network.crosses_eq_true _).mp (crossing depth)
    | true => exact SimpleGraph.Reachable.refl _⟩

theorem retainedTerminalVertex_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (depth : ℕ) (sourceSide : Bool) :
    (retainedTerminalVertex rule configuration crossing depth sourceSide).val =
      plantedVertex (rule.generation depth).network sourceSide := rfl

theorem retainedPersistentVertexEmbedding_terminal (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (first second : ℕ) (bound : first ≤ second) (sourceSide : Bool) :
    retainedPersistentVertexEmbedding rule configuration coherent first second bound
      (retainedTerminalVertex rule configuration crossing first sourceSide) =
        retainedTerminalVertex rule configuration crossing second sourceSide := by
  apply Subtype.ext
  exact persistentVertexEmbedding_planted rule first second bound sourceSide

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

def actualChemicalTerminal (sourceSide : Bool) :
    ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence :=
  actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive childConvergence
    0 (retainedTerminalVertex rule configuration crossing 0 sourceSide)

theorem actualChemicalTerminal_eq_vertex (depth : ℕ) (sourceSide : Bool) :
    actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
      childConvergence sourceSide =
    actualChemicalVertex rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
      childConvergence depth (retainedTerminalVertex rule configuration crossing depth sourceSide) := by
  unfold actualChemicalTerminal
  rw [actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive limitLength lengthNonnegative lengthPositive
    childConvergence 0 depth (Nat.zero_le depth), retainedPersistentVertexEmbedding_terminal]

def actualFiniteClusterTerminal (depth : ℕ) (sourceSide : Bool) :
    ActualFiniteCluster rule configuration scale scalePositive depth :=
  retainedTerminalVertex rule configuration crossing depth sourceSide

theorem retainedFiniteVertexEmbedding_terminal (age depth : ℕ) (bound : age ≤ depth) (sourceSide : Bool) :
    retainedFiniteVertexEmbedding rule configuration coherent scale scalePositive age depth bound
      (retainedTerminalVertex rule configuration crossing age sourceSide) =
        actualFiniteClusterTerminal rule configuration crossing scale scalePositive depth sourceSide := by
  apply Subtype.ext
  exact persistentVertexEmbedding_planted rule age depth bound sourceSide

theorem actualChemicalTerminal_distance_of_terminal_convergence
    (limit : ℝ) (terminalConvergence : Tendsto (fun depth =>
      (((rule.generation depth).network.openGraph (configuration depth)).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) / scale ^ (depth + 1))
      atTop (𝓝 limit)) :
    dist (actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
        childConvergence true)
      (actualChemicalTerminal rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative lengthPositive
        childConvergence false) = limit := by
  rw [actualChemicalTerminal_eq_vertex rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative
      lengthPositive childConvergence 0 true,
    actualChemicalTerminal_eq_vertex rule classicalRule configuration coherent crossing scale scalePositive limitLength lengthNonnegative
      lengthPositive childConvergence 0 false,
    actualChemicalVertex_distance]
  have persistentConvergence := actual_persistent_skeleton_distances_tendsto rule classicalRule configuration coherent scale scalePositive
    0 (limitLength 0) (childConvergence 0) (((rule.generation 0).network.crosses_eq_true _).mp (crossing 0))
  have equality (depth : ℕ) : persistentNormalizedDistance rule configuration scale 0
      (rule.generation 0).network.source (rule.generation 0).network.target depth =
      (((rule.generation depth).network.openGraph (configuration depth)).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) / scale ^ (depth + 1) := by
    unfold persistentNormalizedDistance
    rw [dif_pos (Nat.zero_le depth)]
    have source := persistentVertexEmbedding_planted rule 0 depth (Nat.zero_le depth) true
    have target := persistentVertexEmbedding_planted rule 0 depth (Nat.zero_le depth) false
    simp only [plantedVertex, Bool.true_eq, Bool.false_eq_true, ↓reduceIte] at source target
    rw [source, target]
  exact tendsto_nhds_unique persistentConvergence (terminalConvergence.congr' (Filter.Eventually.of_forall (fun depth => (equality depth).symm)))

theorem actualFiniteCluster_terminal_distance_tendsto
    (limit : ℝ) (terminalConvergence : Tendsto (fun depth =>
      (((rule.generation depth).network.openGraph (configuration depth)).dist
        (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) / scale ^ (depth + 1))
      atTop (𝓝 limit)) :
    Tendsto (fun depth => dist (actualFiniteClusterTerminal rule configuration crossing scale scalePositive depth true)
      (actualFiniteClusterTerminal rule configuration crossing scale scalePositive depth false)) atTop (𝓝 limit) :=
  terminalConvergence

end
end IGSIII.Chemical.SmallBall
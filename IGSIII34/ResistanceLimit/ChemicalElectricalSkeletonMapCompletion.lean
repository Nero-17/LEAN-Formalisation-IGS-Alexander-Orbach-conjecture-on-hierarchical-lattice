import IGSIII34.ResistanceLimit.ElectricalPersistence

/-! The map sends each original retained birth vertex to precisely the same
birth vertex in the actual electrical completion. A proved finite-level
modulus extends to the genuine common direct-limit skeleton. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

variable (rule : Rule) (classicalRule : rule.Classical)
  (configuration : ∀ depth, Configuration (rule.generation depth).edges)
  (coherent : configurationSequenceCoherent rule configuration)
  (scale : ℝ) (scalePositive : 0 < scale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, configuration depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
        (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))
  (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
  (resistancePositive : ∀ depth edge, 0 < resistance depth edge)
  (resistanceCompatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
    ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
    pairResistance (IGSIII34.Percolation.network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (IGSIII34.Percolation.network (rule.generation depth).network (configuration depth))
      (resistance depth) first last)

def chemicalElectricalSkeletonMapCompletion
    (point : ActualChemicalSkeleton rule classicalRule configuration coherent scale scalePositive lengths
      nonnegative lengthPositive childConvergence) :
    ElectricalSpace rule configuration coherent resistance resistancePositive resistanceCompatible :=
  @UniformSpace.Completion.coe'
    (ElectricalSkeleton rule configuration coherent resistance resistancePositive resistanceCompatible)
    (electricalSkeletonMetricSpace rule configuration coherent resistance resistancePositive resistanceCompatible).toUniformSpace point

theorem chemicalElectricalSkeletonMap_birth_completion
    (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    chemicalElectricalSkeletonMapCompletion rule classicalRule configuration coherent scale scalePositive lengths
      nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible ⟦⟨depth,vertex⟩⟧ =
    electricalVertex rule configuration coherent resistance resistancePositive resistanceCompatible depth vertex := rfl

theorem chemicalElectricalSkeletonMap_uniformContinuous_completion
    (finiteModulus : ∀ epsilon > 0, ∃ coarse : ℕ, ∃ delta > 0,
      ∀ fine (first last : RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network
        (configuration (coarse + fine + 1))),
        dist (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative
          lengthPositive childConvergence (coarse + fine + 1) first)
          (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative
            lengthPositive childConvergence (coarse + fine + 1) last) < delta →
        dist (electricalVertex rule configuration coherent resistance resistancePositive resistanceCompatible
          (coarse + fine + 1) first)
          (electricalVertex rule configuration coherent resistance resistancePositive resistanceCompatible
            (coarse + fine + 1) last) < epsilon) :
    UniformContinuous (chemicalElectricalSkeletonMapCompletion rule classicalRule configuration coherent scale
      scalePositive lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible) := by
  apply Metric.uniformContinuous_iff.mpr
  intro epsilon epsilonPositive
  obtain ⟨coarse, delta, deltaPositive, modulus⟩ := finiteModulus epsilon epsilonPositive
  refine ⟨delta, deltaPositive, ?_⟩
  intro first last small
  obtain ⟨depth, firstVertex, lastVertex, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) first last
  have bornSmall : dist (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative
      lengthPositive childConvergence depth firstVertex)
      (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative
        lengthPositive childConvergence depth lastVertex) < delta := by
    change dist (UniformSpace.Completion.coe' (α := ActualChemicalSkeleton rule classicalRule configuration coherent scale scalePositive
      lengths nonnegative lengthPositive childConvergence) ⟦⟨depth,firstVertex⟩⟧)
      (UniformSpace.Completion.coe' (α := ActualChemicalSkeleton rule classicalRule configuration coherent scale scalePositive
        lengths nonnegative lengthPositive childConvergence) ⟦⟨depth,lastVertex⟩⟧) < delta
    rwa [UniformSpace.Completion.dist_eq]
  have fineSmall : dist (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative
      lengthPositive childConvergence (coarse + depth + 1)
        (retainedPersistentVertexEmbedding rule configuration coherent depth (coarse + depth + 1) (by omega) firstVertex))
      (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative
        lengthPositive childConvergence (coarse + depth + 1)
          (retainedPersistentVertexEmbedding rule configuration coherent depth (coarse + depth + 1) (by omega) lastVertex)) < delta := by
    rw [← actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive lengths nonnegative
      lengthPositive childConvergence depth (coarse + depth + 1) (by omega) firstVertex,
      ← actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive lengths nonnegative
        lengthPositive childConvergence depth (coarse + depth + 1) (by omega) lastVertex]
    exact bornSmall
  change dist (electricalVertex rule configuration coherent resistance resistancePositive resistanceCompatible depth firstVertex)
    (electricalVertex rule configuration coherent resistance resistancePositive resistanceCompatible depth lastVertex) < epsilon
  rw [electricalVertex_persistent rule configuration coherent resistance resistancePositive resistanceCompatible
    depth (coarse + depth + 1) (by omega) firstVertex,
    electricalVertex_persistent rule configuration coherent resistance resistancePositive resistanceCompatible
      depth (coarse + depth + 1) (by omega) lastVertex]
  exact modulus depth _ _ fineSmall

end
end IGSIII34.ResistanceLimit

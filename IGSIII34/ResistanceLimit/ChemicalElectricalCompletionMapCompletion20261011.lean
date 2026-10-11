import IGSIII34.ResistanceLimit.ChemicalElectricalSkeletonMapCompletion20261011

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

def chemicalElectricalCompletionMapCompletion20261011 :
    ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive lengths nonnegative lengthPositive childConvergence →
      ElectricalSpace rule configuration coherent resistance resistancePositive resistanceCompatible :=
  UniformSpace.Completion.extension (chemicalElectricalSkeletonMapCompletion20261011 rule classicalRule configuration coherent scale
    scalePositive lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible)

theorem chemicalElectricalCompletionMap_uniformContinuous_completion20261011 :
    UniformContinuous (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule configuration coherent scale scalePositive
      lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible) :=
  UniformSpace.Completion.uniformContinuous_extension

theorem chemicalElectricalCompletionMap_birth_completion20261011
    (continuousSkeleton : UniformContinuous (chemicalElectricalSkeletonMapCompletion20261011 rule classicalRule configuration coherent scale
      scalePositive lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible))
    (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    chemicalElectricalCompletionMapCompletion20261011 rule classicalRule configuration coherent scale scalePositive lengths nonnegative
      lengthPositive childConvergence resistance resistancePositive resistanceCompatible
      (actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative lengthPositive childConvergence
        depth vertex) = electricalVertex rule configuration coherent resistance resistancePositive resistanceCompatible depth vertex := by
  exact UniformSpace.Completion.extension_coe continuousSkeleton ⟦⟨depth,vertex⟩⟧

theorem chemicalElectricalCompletionMap_surjective_completion20261011
    [CompactSpace (ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive lengths nonnegative lengthPositive childConvergence)]
    (continuousSkeleton : UniformContinuous (chemicalElectricalSkeletonMapCompletion20261011 rule classicalRule configuration coherent scale
      scalePositive lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible)) :
    Function.Surjective (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule configuration coherent scale scalePositive
      lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible) := by
  have continuity := (chemicalElectricalCompletionMap_uniformContinuous_completion20261011 rule classicalRule configuration coherent
    scale scalePositive lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible).continuous
  have closed := (isCompact_range continuity).isClosed
  have dense : DenseRange (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule configuration coherent scale scalePositive
      lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible) := by
    apply (electricalVertex_dense rule configuration coherent resistance resistancePositive resistanceCompatible).mono
    intro point membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    exact ⟨actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative lengthPositive childConvergence
      depth vertex, chemicalElectricalCompletionMap_birth_completion20261011 rule classicalRule configuration coherent scale scalePositive
        lengths nonnegative lengthPositive childConvergence resistance resistancePositive resistanceCompatible continuousSkeleton depth vertex⟩
  apply Set.range_eq_univ.mp
  rw [← closed.closure_eq, dense.closure_range]

end
end IGSIII34.ResistanceLimit

import IGSIII34.ResistanceLimit.SkeletonEnergy

set_option autoImplicit false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII34.Percolation
open IGSIII.Chemical.Substitution

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)

theorem skeleton_vertex_ranges_monotone :
    Monotone (fun depth => Set.range (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth)) := by
  apply monotone_nat_of_le_succ
  intro depth point member
  obtain ⟨vertex, rfl⟩ := member
  exact ⟨retainedOldVertexEmbedding rule configuration coherent depth vertex,
    (electricalSkeletonVertex_old rule configuration coherent resistance positive compatible depth vertex).symm⟩

theorem skeleton_vertex_ranges_exhaustive
    (point : ElectricalSkeleton rule configuration coherent resistance positive compatible) :
    ∃ depth, point ∈ Set.range (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth) := by
  obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) point
  exact ⟨depth, vertex, rfl⟩

end
end IGSIII34.ResistanceLimit

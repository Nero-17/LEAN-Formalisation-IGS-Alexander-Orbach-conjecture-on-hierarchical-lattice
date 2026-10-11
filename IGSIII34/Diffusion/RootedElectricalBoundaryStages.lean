import IGSIII34.Diffusion.RootedElectricalStagePotential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)

theorem rootedElectricalSkeletonPoint_planted (side : Bool) (depth : ℕ) :
    rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible depth
      (plantedVertex (rule.generation depth).network side) =
    rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible 0
      (plantedVertex (rule.generation 0).network side) := by
  induction depth with
  | zero => rfl
  | succ depth induction =>
      rw [← generationOldVertex_planted rule depth side,
        rootedElectricalSkeletonPoint_old, induction]

theorem rootedElectricalStagePotential_boundary_zero
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (side : Bool)
    (boundaryZero : potential (rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible 0
      (plantedVertex (rule.generation 0).network side)) = 0) (depth : ℕ) :
    rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential depth
      (plantedVertex (rule.generation depth).network side) = 0 := by
  by_cases retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
    (plantedVertex (rule.generation depth).network sourceSide) (plantedVertex (rule.generation depth).network side)
  · have atBoundary := congrArg potential
      (rootedElectricalSkeletonPoint_planted rule configuration coherent sourceSide resistance positive compatible side depth)
    rw [boundaryZero] at atBoundary
    simpa only [rootedElectricalStagePotential, rootedElectricalSkeletonPoint, dif_pos retained] using atBoundary
  · simp only [rootedElectricalStagePotential, dif_neg retained]

/-- The all-vertex local stages retain precisely the finite-energy bound of
their intrinsic skeleton function. -/
theorem rootedElectricalStagePotential_finite
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (finite : rootedElectricalIntrinsicFiniteEnergy rule configuration coherent sourceSide resistance positive compatible potential) :
    BddAbove (Set.range (fun depth => sourceComponentEnergy
      (sideNetwork (network (rule.generation depth).network (configuration depth)) sourceSide)
      (resistance depth) (rootedElectricalStagePotential rule configuration coherent sourceSide resistance positive compatible potential depth))) := by
  simpa only [rootedElectricalStagePotential_energy, rootedElectricalIntrinsicFiniteEnergy] using finite

end
end IGSIII34.Diffusion

import IGSIII34.Diffusion.ActualRecoveryIdentificationCompletion
import IGSIII34.Diffusion.UniqueSkeletonLimitCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

/-- The whole genuine original fixed-trace recovery sequence converges on
the actual retained skeleton. Countable compactness supplies subsequences;
the sharp trace limit and proved harmonic uniqueness identify every limit. -/
theorem actualOriginalRecovery_pointwise_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (bound : ℝ) (bounded : ∀ depth vertex, |potentials depth vertex| ≤ bound)
    (restriction : ∀ fine vertex, ((rule.generation coarse).network.openGraph
      (stationaryConfiguration rule marks.val coarse)).Reachable (rule.generation coarse).network.source vertex →
      potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex)
    (energyConvergence : Tendsto (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)) atTop
      (𝓝 (sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val coarse) boundary))) :
    ∀ point, Tendsto
      (fun depth => actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive
        marks potentials depth point) atTop
      (𝓝 (actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary point)) := by
  letI := countable_actualEnergySkeleton_completion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
  exact bounded_countable_unique_limit_tendsto_completion
    (actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    bound (actualMicroscopicHarmonicLift_bounded_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks stationary potentials bound (fun depth vertex _ => bounded depth vertex))
    (actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary)
    (fun selected selectedStrict candidate convergence =>
      actualOriginalRecovery_limit_identification_completion rule p positive belowOne fixedPoint growth value growthPositive
        marks fieldLimit coarse boundary potentials restriction energyConvergence selected selectedStrict candidate convergence)

theorem actualOriginalRecovery_old_values_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (bound : ℝ) (bounded : ∀ depth vertex, |potentials depth vertex| ≤ bound)
    (restriction : ∀ fine vertex, ((rule.generation coarse).network.openGraph
      (stationaryConfiguration rule marks.val coarse)).Reachable (rule.generation coarse).network.source vertex →
      potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex)
    (energyConvergence : Tendsto (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)) atTop
      (𝓝 (sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val coarse) boundary)))
    (old : ℕ) (vertex : RetainedSkeletonVertex (rule.generation old).network (stationaryConfiguration rule marks.val old)) :
    Tendsto (fun fine => potentials (old + fine + 1) (blockOldVertexEmbedding rule old fine vertex.val)) atTop
      (𝓝 (actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
        (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) old vertex.val))) := by
  have pointwise := actualOriginalRecovery_pointwise_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks stationary fieldLimit coarse boundary potentials bound bounded restriction energyConvergence
    (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) old vertex.val)
  have ages : Tendsto (fun fine : ℕ => old + fine + 1) atTop atTop := by
    convert tendsto_add_atTop_nat (old + 1) using 1
    funext fine
    omega
  exact (pointwise.comp ages).congr' (Eventually.of_forall fun fine =>
    actualMicroscopicHarmonicLift_old_consistent_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks potentials old fine vertex.val vertex.property)

end
end IGSIII34.Diffusion

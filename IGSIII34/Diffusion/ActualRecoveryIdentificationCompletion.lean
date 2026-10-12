import IGSIII34.Diffusion.ActualOriginalCompactnessCompletion
import IGSIII34.Diffusion.HarmonicBoundaryUniquenessCompletion
import IGSIII34.Diffusion.OriginalRecoveryReindexCompletion

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

/-- Any pointwise subsequential limit of the genuine fixed-trace original
recovery functions is identified with the actual stationary harmonic
function by sharp original-energy lower semicontinuity and retained
boundary uniqueness. -/
theorem actualOriginalRecovery_limit_identification_completion
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (restriction : ∀ fine vertex, ((rule.generation coarse).network.openGraph
      (stationaryConfiguration rule marks.val coarse)).Reachable (rule.generation coarse).network.source vertex →
      potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex)
    (energyConvergence : Tendsto (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)) atTop
      (𝓝 (sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val coarse) boundary)))
    (selected : ℕ → ℕ) (selectedStrict : StrictMono selected)
    (candidate : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ)
    (pointwiseConvergence : ∀ point, Tendsto
      (fun index => actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive
        marks potentials (selected index) point) atTop (𝓝 (candidate point))) :
    candidate = actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary := by
  have limitEnergy := energyConvergence.comp selectedStrict.tendsto_atTop
  obtain ⟨finite, energyUpper⟩ := actualOriginal_subsequence_energy_lower_completion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) fieldLimit potentials
    (actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    (actualMicroscopicHarmonicLift_old_consistent_completion rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    selected selectedStrict.tendsto_atTop candidate pointwiseConvergence _ limitEnergy
  have boundaryMatches (vertex : RetainedSkeletonVertex (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) :
      candidate (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) coarse vertex.val) = boundary vertex.val := by
    have eventuallyBoundary : ∀ᶠ index in atTop,
        actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive marks potentials
          (selected index) (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) coarse vertex.val) = boundary vertex.val := by
      filter_upwards [selectedStrict.tendsto_atTop.eventually (eventually_ge_atTop (coarse + 1))] with index large
      let fine := selected index - coarse - 1
      have identity : selected index = coarse + fine + 1 := by dsimp [fine]; omega
      rw [identity, actualMicroscopicHarmonicLift_old_consistent_completion rule p positive belowOne fixedPoint growth value
        growthPositive marks potentials coarse fine vertex.val vertex.property]
      exact restriction fine vertex.val vertex.property
    exact tendsto_nhds_unique (pointwiseConvergence _)
      (tendsto_const_nhds.congr' (eventuallyBoundary.mono fun _ equality => equality.symm))
  apply harmonicTowerFunction_unique_boundary_completion rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    marks.property.1.1.2.2 marks.property.2 marks.property.1.2 coarse boundary ⟨candidate, finite⟩
  · intro vertex
    have equality := boundaryMatches vertex
    change candidate (electricalSkeletonPoint rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
      marks.property.1.1.2.2 coarse vertex.val) = boundary vertex.val at equality
    rw [electricalSkeletonPoint_retained] at equality
    exact equality
  · exact energyUpper

end
end IGSIII34.Diffusion

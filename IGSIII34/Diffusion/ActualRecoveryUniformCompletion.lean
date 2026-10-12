import IGSIII34.Diffusion.ActualRecoveryPointwiseCompletion
import IGSIII34.Diffusion.OriginalValuesUniformCompletion
import IGSIII34.Diffusion.SourceEnergyScaleCompletion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms IGSIII34.Spectral MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

theorem actualHarmonicCompletion_retained_vertex_completion
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ depth vertex) =
    actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
      (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) depth vertex.val) := by
  unfold actualHarmonicCompletionFunctionCompletion actualEnergyFiniteVertexCompletion
  rw [electricalSkeletonPoint_retained]
  exact completionExtension_coe
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    ⟨actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary,
      actualHarmonicFunction_finite rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary⟩
    _

/-- Real original fixed-trace minimizers converge uniformly over every
embedded retained finite vertex to the actual stationary harmonic extension.
The proof does not require uniform energy bounds for their stationary lifts. -/
theorem actualOriginalRecovery_uniform_completion
    [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩)]
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
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
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth),
        |potentials depth vertex.val -
          actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ depth vertex)| < tolerance := by
  obtain ⟨energyBound, energyBoundNonnegative, energiesBounded⟩ := convergent_nonnegative_uniform_upper_completion _ _ energyConvergence
  apply originalPotential_values_uniform_completion rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound potentials
    (actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary)
    _ energyBound energyBoundNonnegative
  · intro depth
    rw [← sourceEnergy_constant_inverse_scale_completion]
    exact energiesBounded depth
  · intro old vertex
    have anchorValue := actualHarmonicCompletion_retained_vertex_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks coarse boundary old vertex
    have convergence := actualOriginalRecovery_old_values_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks stationary fieldLimit coarse boundary potentials bound bounded restriction energyConvergence old vertex
    exact Eq.mp (congrArg (fun target : ℝ => Tendsto
      (fun fine => potentials (old + fine + 1) (blockOldVertexEmbedding rule old fine vertex.val)) atTop (𝓝 target)) anchorValue.symm) convergence

end
end IGSIII34.Diffusion

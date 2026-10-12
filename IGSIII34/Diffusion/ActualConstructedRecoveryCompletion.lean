import IGSIII34.Diffusion.ActualRecoveryUniformCompletion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms IGSIII34.Spectral MeasureTheory Filter
open scoped BigOperators _root_.Topology

/-- For every actual coarse boundary, bounded original-network recovery
potentials are constructed, with exact energy convergence and uniform
convergence at every retained embedded vertex to the actual harmonic extension. -/
theorem exists_actualOriginal_uniform_trace_recovery_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (growthPositive : 0 < growth)
    (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
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
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ) :
    ∃ potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ,
      (∀ depth vertex, |potentials depth vertex| ≤ ∑ vertex, |boundary vertex|) ∧
      (∀ fine vertex, ((rule.generation coarse).network.openGraph (stationaryConfiguration rule marks.val coarse)).Reachable
        (rule.generation coarse).network.source vertex →
        potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex) = boundary vertex) ∧
      Tendsto (fun depth => sourceComponentEnergy
        (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)) atTop
        (𝓝 (sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse))
          (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val coarse) boundary)) ∧
      ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
        ∀ vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth),
          |potentials depth vertex.val -
            actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
              (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
                ⟨marks.val, marks.property.1.1⟩ depth vertex)| < tolerance := by
  classical
  have boundaryBound (vertex : Fin (rule.generation coarse).vertices) : |boundary vertex| ≤ ∑ vertex, |boundary vertex| :=
    Finset.single_le_sum (fun point _ => abs_nonneg (boundary point)) (Finset.mem_univ vertex)
  obtain ⟨potentials, bounded, restriction, energies⟩ := exists_actual_bounded_global_trace_recovery_completion
    rule marks.val marks.property.1.1.2.1 growth growthPositive
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    marks.property.1.1.1 fieldLimit coarse boundary (∑ vertex, |boundary vertex|)
    (Finset.sum_nonneg fun vertex _ => abs_nonneg (boundary vertex)) (fun vertex _ => boundaryBound vertex)
  simp only [graph_eq_openGraph] at restriction
  refine ⟨potentials, bounded, restriction, energies, ?_⟩
  exact actualOriginalRecovery_uniform_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound
    coarse boundary potentials (∑ vertex, |boundary vertex|) bounded restriction energies

end
end IGSIII34.Diffusion

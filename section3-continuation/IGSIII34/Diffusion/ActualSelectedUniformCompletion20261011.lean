import IGSIII34.Diffusion.OriginalSelectedValuesUniformCompletion20261011
import IGSIII34.Diffusion.ActualRecoveryUniformCompletion20261011
import IGSIII34.Diffusion.ActualOriginalEnergyCompactnessCompletion20261011

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

theorem actualEnergyExtension_retained_vertex_completion20261011
    (candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (depth : ℕ) (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ depth vertex) =
    candidate.val (actualEnergyFiniteVertexCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) depth vertex.val) := by
  unfold actualEnergyFiniteVertexCompletion20261011
  rw [electricalSkeletonPoint_retained]
  exact completionExtension_coe
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) candidate _

/-- Every actual finite-energy selected skeleton limit is also the uniform
limit on all vertices of the corresponding original finite generations. -/
theorem actualOriginal_selected_uniform_completion20261011
    [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩)]
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (energyBound : ∀ depth, sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth) ≤ bound)
    (candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (convergence : ∀ point, Tendsto
      (fun index => actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks potentials (selected index) point) atTop (𝓝 (candidate.val point))) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
        |potentials (selected index) vertex.val -
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)| < tolerance := by
  have oldConvergence (coarse : ℕ) (vertex : RetainedSkeletonVertex (rule.generation coarse).network
      (stationaryConfiguration rule marks.val coarse)) : Tendsto
      (fun index => originalRetainedOldValueCompletion20261011 rule potentials coarse vertex.val (selected index)) atTop
      (𝓝 (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate
        (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩ coarse vertex))) := by
    have sourceConvergence := convergence (actualEnergyFiniteVertexCompletion20261011 rule p positive belowOne fixedPoint growth value
      growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) coarse vertex.val)
    have identical : ∀ᶠ index in atTop,
        actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks potentials
          (selected index) (actualEnergyFiniteVertexCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) coarse vertex.val) =
        originalRetainedOldValueCompletion20261011 rule potentials coarse vertex.val (selected index) := by
      filter_upwards [selectedAtTop.eventually (eventually_ge_atTop (coarse + 1))] with index large
      obtain ⟨fine, identity⟩ : ∃ fine, selected index = coarse + fine + 1 :=
        ⟨selected index - coarse - 1, by omega⟩
      rw [identity, actualMicroscopicHarmonicLift_old_consistent_completion20261011 rule p positive belowOne fixedPoint growth value
        growthPositive marks potentials coarse fine vertex.val vertex.property,
        originalRetainedOldValueCompletion20261011, dif_pos (by omega : coarse ≤ coarse + fine + 1),
        ← blockOldVertexEmbedding_eq_persistent]
    have oldLimit := sourceConvergence.congr' identical
    have valueIdentity := actualEnergyExtension_retained_vertex_completion20261011 rule p positive belowOne fixedPoint growth value
      growthPositive marks candidate coarse vertex
    exact Eq.mp (congrArg (fun target : ℝ => Tendsto
      (fun index => originalRetainedOldValueCompletion20261011 rule potentials coarse vertex.val (selected index)) atTop
        (𝓝 target)) valueIdentity.symm) oldLimit
  exact originalPotential_selected_values_uniform_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound potentials
    (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate)
    selected selectedAtTop oldConvergence bound boundNonnegative (fun depth => by
      rw [← sourceEnergy_constant_inverse_scale_completion20261011]
      exact energyBound depth)

end
end IGSIII34.Diffusion

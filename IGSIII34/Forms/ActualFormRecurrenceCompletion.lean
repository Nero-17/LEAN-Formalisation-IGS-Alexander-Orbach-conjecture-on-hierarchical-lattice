import IGSIII34.Spectral.ActualResolventConservationCompletion

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality IGSIII34.ResistanceLimit IGSIII34.Spectral MeasureTheory Filter
open IGSIII.Chemical.Substitution
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualRecurrenceMeasurableCompletion : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := borel _
local instance actualRecurrenceBorelCompletion : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := ⟨rfl⟩

/-- The actual finite-energy domain satisfies the usual recurrence
approximation criterion: bounded domain functions tend to one and their
energies tend to zero. Here the constant one itself supplies the entire
sequence. This is analytic form recurrence, not an assumed path-hitting
or stopping-time conclusion. -/
theorem actual_form_recurrence_approximation_completion :
    ∃ potentials : ℕ → actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor,
      (∀ index point, 0 ≤ actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
        (potentials index) point ∧ actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
        (potentials index) point ≤ 1) ∧
      (∀ point, Tendsto (fun index => actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
        (potentials index) point) atTop (𝓝 1)) ∧
      Tendsto (fun index => limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) (potentials index).val) atTop (𝓝 0) := by
  refine ⟨fun _ => actualEnergyConstantCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor 1, ?_, ?_, ?_⟩
  · intro index point
    rw [actualEnergyConstant_extension_completion]
    exact ⟨zero_le_one, le_refl _⟩
  · intro point
    simpa only [actualEnergyConstant_extension_completion] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  · have zero : limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConstantCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor 1).val = 0 := by
      change (⨆ depth, finiteEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks depth)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks depth) (fun _ => (1:ℝ))) = 0
      simp only [finiteEnergy_constant, ciSup_const]
    simpa only [zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end
end IGSIII34.Forms

import IGSIII34.Spectral.ActualBoundaryHarmonicCompletion
import IGSIII34.ResistanceLimit.HarmonicTowerComponentBoundsCompletion
import IGSIII34.ResistanceLimit.ElectricalPersistence

/-! The actual continuous harmonic interpolation preserves the entire range
of the retained initial boundary, including every hanging component. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Spectral IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

theorem actual_harmonic_fine_boundary_deviation_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ) (reference error : ℝ)
    (boundaryBound : ∀ vertex, ((rule.generation coarse).network.openGraph
      (stationaryConfiguration rule marks.val coarse)).Reachable (rule.generation coarse).network.source vertex →
      |boundary vertex - reference| ≤ error)
    (vertex : RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network
      (stationaryConfiguration rule marks.val (coarse + fine + 1))) :
    |actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
      coarse boundary (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩ (coarse + fine + 1) vertex) - reference| ≤ error := by
  rw [show actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
      coarse boundary (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩ (coarse + fine + 1) vertex) =
      actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
        (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
          (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
          (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
          (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
            ⟨marks.val,marks.property.1.1⟩) marks.property.1.1.2.2 (coarse + fine + 1) vertex) from
    completionExtension_coe
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      ⟨_, actualHarmonicFunction_finite rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary⟩ _]
  rw [actualHarmonicFunction_retained_completion rule p positive belowOne fixedPoint growth value growthPositive marks
    coarse boundary (coarse + fine + 1) (by omega)]
  obtain ⟨edge, child, side, identity, reachable, _⟩ := actual_retained_generation_available_cell_cover
    rule marks.val marks.property.1.1.2.1 coarse fine vertex.val vertex.property
  rw [identity]
  refine stationary_harmonic_tower_component_deviation_completion rule marks.val
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) growth growthPositive
    marks.property.1.1.1 marks.property.1.1.2.1 stationary [] true
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    marks.property.2 coarse fine boundary edge reference error child ?_ ?_ (identity ▸ vertex.property)
  · intro availableSide localReachable
    exact boundaryBound _ (actual_available_block_anchor_retained_completion rule marks.val
      marks.property.1.1.2.1 coarse fine [] true edge availableSide child localReachable (identity ▸ vertex.property))
  · cases side
    · exact Or.inr reachable
    · exact Or.inl reachable

theorem actual_harmonic_completion_boundary_deviation_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ) (reference error : ℝ)
    (boundaryBound : ∀ vertex, ((rule.generation coarse).network.openGraph
      (stationaryConfiguration rule marks.val coarse)).Reachable (rule.generation coarse).network.source vertex →
      |boundary vertex - reference| ≤ error)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) :
    |actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
      coarse boundary point - reference| ≤ error := by
  have closed : IsClosed {point | |actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value
      growthPositive marks coarse boundary point - reference| ≤ error} :=
    isClosed_le (((actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
      coarse boundary).continuous.sub continuous_const).abs) continuous_const
  have contains : (⋃ depth, Set.range (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val,marks.property.1.1⟩ depth)) ⊆ {point | |actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint
      growth value growthPositive marks coarse boundary point - reference| ≤ error} := by
    intro point membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    change |actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
      (electricalVertex rule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
        marks.property.1.1.2.2 depth vertex) - reference| ≤ error
    rw [electricalVertex_persistent rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2 depth (coarse + depth + 1) (by omega)]
    exact actual_harmonic_fine_boundary_deviation_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks stationary coarse depth boundary reference error boundaryBound _
  have full := closure_minimal contains closed
  rw [(actualStationaryElectricalVertex_dense rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val,marks.property.1.1⟩).closure_eq] at full
  exact full (Set.mem_univ point)

theorem actual_harmonic_completion_unit_interval_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (boundaryBound : ∀ vertex, ((rule.generation coarse).network.openGraph (stationaryConfiguration rule marks.val coarse)).Reachable
      (rule.generation coarse).network.source vertex → 0 ≤ boundary vertex ∧ boundary vertex ≤ 1)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) :
    0 ≤ actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary point ∧
    actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary point ≤ 1 := by
  have bound := actual_harmonic_completion_boundary_deviation_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks stationary coarse boundary (1/2) (1/2) (by
      intro vertex retained
      exact abs_le.mpr ⟨by linarith [(boundaryBound vertex retained).1], by linarith [(boundaryBound vertex retained).2]⟩) point
  have both := abs_le.mp bound
  constructor <;> linarith

end
end IGSIII34.ResistanceLimit

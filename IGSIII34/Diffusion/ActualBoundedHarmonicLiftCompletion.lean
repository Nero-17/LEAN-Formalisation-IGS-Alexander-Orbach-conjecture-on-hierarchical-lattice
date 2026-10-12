import IGSIII34.Diffusion.ActualSubsequenceEnergyLowerCompletion
import IGSIII34.ResistanceLimit.ActualHarmonicGlobalRangeCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true

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

def actualMicroscopicHarmonicLiftCompletion
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) (depth : ℕ) :
    ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ :=
  actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks depth (potentials depth)

theorem actualMicroscopicHarmonicLift_bounded_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) (bound : ℝ)
    (bounded : ∀ depth vertex, ((rule.generation depth).network.openGraph
      (stationaryConfiguration rule marks.val depth)).Reachable (rule.generation depth).network.source vertex →
      |potentials depth vertex| ≤ bound) :
    ∀ depth point, |actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks potentials depth point| ≤ bound := by
  intro depth point
  have estimate := actual_harmonic_completion_boundary_deviation_completion rule p positive belowOne fixedPoint growth value
    growthPositive marks stationary depth (potentials depth) 0 bound (by
      intro vertex retained
      simpa only [sub_zero] using bounded depth vertex retained) (point : UniformSpace.Completion _)
  have values : actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value
      growthPositive marks depth (potentials depth)
      (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) =
      actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive marks potentials depth point := by
    exact completionExtension_coe
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      ⟨actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks depth (potentials depth),
        actualHarmonicFunction_finite rule p positive belowOne fixedPoint growth value growthPositive marks depth (potentials depth)⟩
      point
  rw [values, sub_zero] at estimate
  exact estimate

theorem actualMicroscopicHarmonicLift_old_consistent_completion
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (coarse fine : ℕ) (vertex : Fin (rule.generation coarse).vertices)
    (retained : ((rule.generation coarse).network.openGraph (stationaryConfiguration rule marks.val coarse)).Reachable
      (rule.generation coarse).network.source vertex) :
    actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive marks potentials
      (coarse + fine + 1) (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) coarse vertex) =
      potentials (coarse + fine + 1) (blockOldVertexEmbedding rule coarse fine vertex) := by
  let coherent := typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩
  let resistance := stationaryResistance rule p positive belowOne fixedPoint growth value marks.val
  let resistancePositive := typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩
  let coarseVertex : RetainedSkeletonVertex (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse) :=
    ⟨vertex, retained⟩
  have persistence := electricalVertex_persistent rule (stationaryConfiguration rule marks.val) coherent resistance resistancePositive
    marks.property.1.1.2.2 coarse (coarse + fine + 1) (by omega) coarseVertex
  have skeletonPersistence : electricalSkeletonVertex rule (stationaryConfiguration rule marks.val) coherent resistance resistancePositive
      marks.property.1.1.2.2 coarse coarseVertex =
      electricalSkeletonVertex rule (stationaryConfiguration rule marks.val) coherent resistance resistancePositive
        marks.property.1.1.2.2 (coarse + fine + 1)
        (retainedPersistentVertexEmbedding rule (stationaryConfiguration rule marks.val) coherent coarse (coarse + fine + 1) (by omega) coarseVertex) := by
    apply UniformSpace.Completion.coe_isometry.injective
    exact persistence
  change actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks (coarse + fine + 1)
    (potentials (coarse + fine + 1)) (electricalSkeletonPoint rule (stationaryConfiguration rule marks.val) coherent resistance
      resistancePositive marks.property.1.1.2.2 coarse vertex) = _
  rw [electricalSkeletonPoint_retained rule (stationaryConfiguration rule marks.val) coherent resistance resistancePositive
    marks.property.1.1.2.2 coarse coarseVertex, skeletonPersistence,
    actualHarmonicFunction_boundary rule p positive belowOne fixedPoint growth value growthPositive marks]
  simp only [retainedPersistentVertexEmbedding_val]
  rw [← blockOldVertexEmbedding_eq_persistent]

theorem actualMicroscopicHarmonicLift_pointwise_subsequence_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) (bound : ℝ)
    (bounded : ∀ depth vertex, ((rule.generation depth).network.openGraph
      (stationaryConfiguration rule marks.val depth)).Reachable (rule.generation depth).network.source vertex →
      |potentials depth vertex| ≤ bound) :
    ∃ limitPotential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ,
      ∃ selected : ℕ → ℕ, StrictMono selected ∧ (∀ point, |limitPotential point| ≤ bound) ∧
      ∀ point, Tendsto (fun index => actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value
        growthPositive marks potentials (selected index) point) atTop (𝓝 (limitPotential point)) := by
  letI := countable_actualEnergySkeleton_completion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
  exact bounded_countable_potentials_subsequence_completion
    (actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    bound (actualMicroscopicHarmonicLift_bounded_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks stationary potentials bound bounded)

end
end IGSIII34.Diffusion

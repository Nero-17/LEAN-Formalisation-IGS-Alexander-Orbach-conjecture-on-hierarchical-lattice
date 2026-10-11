import IGSIII34.Diffusion.ActualBoundedHarmonicLiftCompletion20261011

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

/-- Every genuinely bounded microscopic voltage/energy family has a
subsequence with an actual finite-energy skeleton limit. The energy
coordinate is extracted together with all skeleton values, and its lower
bound is proved from the original unit-edge finite traces. -/
theorem actualOriginal_bounded_energy_subsequence_completion20261011
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) (voltageBound energyBound : ℝ)
    (boundedVoltage : ∀ depth vertex, ((rule.generation depth).network.openGraph
      (stationaryConfiguration rule marks.val depth)).Reachable (rule.generation depth).network.source vertex →
      |potentials depth vertex| ≤ voltageBound)
    (boundedEnergy : ∀ depth, sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth) ≤ energyBound) :
    ∃ candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks),
      ∃ selected : ℕ → ℕ, StrictMono selected ∧
      ∃ limitEnergy : ℝ, limitEnergy ≤ energyBound ∧
      Tendsto (fun index => sourceComponentEnergy
        (network (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)))
        (fun _ => (growth ^ (selected index + 1))⁻¹) (potentials (selected index))) atTop (𝓝 limitEnergy) ∧
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) candidate.val ≤ limitEnergy ∧
      ∀ point, Tendsto (fun index => actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value
        growthPositive marks potentials (selected index) point) atTop (𝓝 (candidate.val point)) := by
  classical
  letI := countable_actualEnergySkeleton_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
  let energies (depth : ℕ) := sourceComponentEnergy
    (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)
  let functions := actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks potentials
  let coordinates (depth : ℕ) (point : Option (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) : ℝ :=
    match point with | none => energies depth | some point => functions depth point
  have functionsBounded := actualMicroscopicHarmonicLift_bounded_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks stationary potentials voltageBound boundedVoltage
  have coordinatesBounded : ∀ depth point, |coordinates depth point| ≤ max voltageBound energyBound := by
    intro depth point
    cases point with
    | none =>
      have nonnegative := sourceComponentEnergy_nonnegative
        (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (fun _ => (growth ^ (depth + 1))⁻¹) (fun _ => inv_pos.mpr (pow_pos growthPositive _)) (potentials depth)
      have absBound : |energies depth| ≤ energyBound := by
        rw [abs_of_nonneg nonnegative]
        exact boundedEnergy depth
      exact absBound.trans (le_max_right _ _)
    | some point => exact (functionsBounded depth point).trans (le_max_left _ _)
  obtain ⟨limitCoordinates, selected, strict, _, convergence⟩ :=
    bounded_countable_potentials_subsequence_completion20261011 coordinates (max voltageBound energyBound) coordinatesBounded
  let limitPotential := fun point => limitCoordinates (some point)
  have pointwise : ∀ point, Tendsto (fun index => functions (selected index) point) atTop (𝓝 (limitPotential point)) :=
    fun point => convergence (some point)
  have energyConvergence : Tendsto (fun index => energies (selected index)) atTop (𝓝 (limitCoordinates none)) :=
    convergence none
  have energyUpper : limitCoordinates none ≤ energyBound :=
    le_of_tendsto energyConvergence (Eventually.of_forall fun index => boundedEnergy (selected index))
  obtain ⟨finite, below⟩ := actualOriginal_subsequence_energy_lower_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) fieldLimit potentials functions
    (actualMicroscopicHarmonicLift_old_consistent_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    selected strict.tendsto_atTop limitPotential pointwise (limitCoordinates none) energyConvergence
  exact ⟨⟨limitPotential, finite⟩, selected, strict, limitCoordinates none, energyUpper, energyConvergence, below, pointwise⟩

end
end IGSIII34.Diffusion

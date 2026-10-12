import IGSIII34.Diffusion.ActualOriginalEnergyCompactnessCompletion

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

/-- If a genuine original family has a selected pointwise limit, an energy
subselection retains that same limit and proves its actual finite energy.
This supplies the sharp bound needed for whole-sequence uniqueness. -/
theorem actualOriginal_prescribed_limit_energy_completion
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ) (energyBound : ℝ)
    (boundedEnergy : ∀ depth, sourceComponentEnergy
      (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth) ≤ energyBound)
    (outer : ℕ → ℕ) (outerStrict : StrictMono outer)
    (limitPotential : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) → ℝ)
    (pointwise : ∀ point, Tendsto (fun index => actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value
      growthPositive marks potentials (outer index) point) atTop (𝓝 (limitPotential point))) :
    ∃ inner : ℕ → ℕ, StrictMono inner ∧
      ∃ limitEnergy : ℝ, limitEnergy ≤ energyBound ∧
      ∃ candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks), candidate.val = limitPotential ∧
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) candidate.val ≤ limitEnergy ∧
      Tendsto (fun index => sourceComponentEnergy
        (network (rule.generation (outer (inner index))).network (stationaryConfiguration rule marks.val (outer (inner index))))
        (fun _ => (growth ^ (outer (inner index) + 1))⁻¹) (potentials (outer (inner index)))) atTop (𝓝 limitEnergy) := by
  let energies (depth : ℕ) := sourceComponentEnergy
    (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (fun _ => (growth ^ (depth + 1))⁻¹) (potentials depth)
  have energyNonnegative (depth : ℕ) : 0 ≤ energies depth :=
    sourceComponentEnergy_nonnegative (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) (fun _ => inv_pos.mpr (pow_pos growthPositive _)) (potentials depth)
  obtain ⟨energyFunction, inner, strict, _, energyConvergence⟩ :=
    bounded_countable_potentials_subsequence_completion (fun index (_ : Unit) => energies (outer index)) energyBound
      (fun index _ => by rw [abs_of_nonneg (energyNonnegative (outer index))]; exact boundedEnergy (outer index))
  have convergence : Tendsto (fun index => energies (outer (inner index))) atTop (𝓝 (energyFunction ())) := energyConvergence ()
  obtain ⟨finite, below⟩ := actualOriginal_subsequence_energy_lower_completion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) fieldLimit potentials
    (actualMicroscopicHarmonicLiftCompletion rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    (actualMicroscopicHarmonicLift_old_consistent_completion rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    (outer ∘ inner) (outerStrict.comp strict).tendsto_atTop limitPotential
    (fun point => (pointwise point).comp strict.tendsto_atTop) (energyFunction ()) convergence
  exact ⟨inner, strict, energyFunction (), le_of_tendsto convergence
    (Eventually.of_forall fun index => boundedEnergy (outer (inner index))), ⟨limitPotential, finite⟩, rfl, below, convergence⟩

end
end IGSIII34.Diffusion

import IGSIII34.ResistanceLimit.HarmonicVariational
import IGSIII34.ResistanceLimit.EnergyVariational

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped Topology

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)
variable (minimizer : ∀ depth (boundary : Fin (rule.generation depth).vertices → ℝ),
  ∃ potential : Fin (rule.generation (depth + 1)).vertices → ℝ,
    (∀ vertex, ((rule.generation depth).network.openGraph (configuration depth)).Reachable
        (rule.generation depth).network.source vertex →
      potential (rule.generationOldVertex depth vertex) = boundary vertex) ∧
    sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) potential =
    sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth) boundary)
variable (sourceEnergyLe : ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
  sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth)
    (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
  sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
    (resistance (depth + 1)) potential)

include sourceEnergyLe in
theorem harmonicTowerFunction_orthogonal (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (perturbation : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive))
    (zero : ∀ vertex : RetainedSkeletonVertex (rule.generation initial).network (configuration initial),
      perturbation.val (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) = 0) :
    limitingPairing (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary)
      perturbation.val = 0 := by
  have finite := harmonicTowerFunction_finite rule configuration coherent resistance positive compatible minimizer sourceEnergyLe
    initial boundary
  apply limitingPairing_eq_zero_of_minimal _ _ _
    (skeleton_traceEnergy_monotone rule configuration coherent resistance positive compatible sourceEnergyLe)
    finite perturbation.property
  intro scalar
  apply harmonicTowerFunction_minimal rule configuration coherent resistance positive compatible minimizer sourceEnergyLe
    initial boundary
    ⟨(fun point => harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary point +
        scalar * perturbation.val point),
      (energyDomain _ _ _).add_mem finite ((energyDomain _ _ _).smul_mem scalar perturbation.property)⟩
  intro vertex
  change harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary
    (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) +
      scalar * perturbation.val (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) = _
  rw [harmonicTowerFunction_boundary, zero vertex, mul_zero, add_zero]

def harmonicInterpolation (initial : ℕ)
    (potential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ) :
    ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ :=
  harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial
    (fun vertex => potential (electricalSkeletonPoint rule configuration coherent resistance positive compatible initial vertex))

include sourceEnergyLe in
theorem harmonicInterpolation_finite (initial : ℕ)
    (potential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ) :
    harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential ∈
      energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance)
        (skeletonEnergyConductance_nonnegative rule configuration resistance positive) :=
  harmonicTowerFunction_finite rule configuration coherent resistance positive compatible minimizer sourceEnergyLe initial _

theorem harmonicInterpolation_boundary (initial : ℕ)
    (potential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ)
    (vertex : RetainedSkeletonVertex (rule.generation initial).network (configuration initial)) :
    harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential
      (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) =
      potential (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) := by
  unfold harmonicInterpolation
  rw [harmonicTowerFunction_boundary, electricalSkeletonPoint_retained]

include sourceEnergyLe in
theorem harmonicInterpolation_residual_energy (initial : ℕ)
    (potential : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive)) :
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (fun point => potential.val point -
        harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point) =
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) potential.val -
    traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) initial potential.val := by
  have interpolationFinite := harmonicInterpolation_finite rule configuration coherent resistance positive compatible minimizer
    sourceEnergyLe initial potential.val
  have residualFinite : (fun point => potential.val point -
      harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point) ∈
      energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance)
        (skeletonEnergyConductance_nonnegative rule configuration resistance positive) :=
    (energyDomain _ _ _).sub_mem potential.property interpolationFinite
  have orthogonal := harmonicTowerFunction_orthogonal rule configuration coherent resistance positive compatible minimizer
    sourceEnergyLe initial
    (fun vertex => potential.val (electricalSkeletonPoint rule configuration coherent resistance positive compatible initial vertex))
    ⟨(fun point => potential.val point -
      harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point), residualFinite⟩
    (fun vertex => by
      change potential.val _ - harmonicInterpolation rule configuration coherent resistance positive compatible minimizer
        initial potential.val _ = 0
      rw [harmonicInterpolation_boundary, sub_self])
  have sumIdentity := limitingEnergy_add_identity
    (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
    (skeletonEnergyConductance rule configuration resistance)
    (harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val)
    (fun point => potential.val point -
      harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point)
  have values : (fun point => harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point +
      (potential.val point - harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point)) =
      potential.val := by funext point; ring
  rw [values] at sumIdentity
  change limitingPairing _ _
    (harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val) _ = 0 at orthogonal
  rw [orthogonal, mul_zero, add_zero] at sumIdentity
  have energy := harmonic_interpolation_energy rule configuration coherent resistance positive compatible minimizer sourceEnergyLe initial potential.val
  change limitingEnergy _ _ (harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val) = _ at energy
  linarith

include sourceEnergyLe in
theorem harmonicInterpolation_residual_energy_tendsto
    (potential : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive)) :
    Tendsto (fun initial => limitingEnergy
      (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (fun point => potential.val point -
        harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point))
      atTop (𝓝 0) := by
  simp_rw [harmonicInterpolation_residual_energy rule configuration coherent resistance positive compatible minimizer sourceEnergyLe]
  have convergence := (tendsto_const_nhds (x := limitingEnergy
    (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
    (skeletonEnergyConductance rule configuration resistance) potential.val)).sub (traceEnergy_tendsto
    (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
    (skeletonEnergyConductance rule configuration resistance)
    (skeletonEnergyConductance_nonnegative rule configuration resistance positive) potential.property
    (skeleton_traceEnergy_monotone rule configuration coherent resistance positive compatible sourceEnergyLe potential.val))
  simpa only [sub_self] using convergence

end
end IGSIII34.ResistanceLimit

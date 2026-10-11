import IGSIII34.ResistanceLimit.HarmonicDensity

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

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
/-- Any finite-energy candidate with no more energy than its prescribed
old trace is the unique harmonic interpolation. This identifies recovery
limits through genuine energy minimisation, rather than assumed
convergence of finite harmonic coefficients. -/
theorem harmonicInterpolation_unique_of_trace_energy_completion20261011
    (initial : ℕ)
    (potential : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive))
    (energyUpper : limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) potential.val ≤
      traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance) initial potential.val) :
    potential.val = harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val := by
  have harmonicFinite := harmonicInterpolation_finite rule configuration coherent resistance positive compatible
    minimizer sourceEnergyLe initial potential.val
  let residual : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive) :=
    ⟨fun point => potential.val point -
      harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point,
      (energyDomain _ _ _).sub_mem potential.property harmonicFinite⟩
  have residualIdentity := harmonicInterpolation_residual_energy rule configuration coherent resistance positive compatible
    minimizer sourceEnergyLe initial potential
  have residualZero : limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) residual.val = 0 := by
    apply le_antisymm
    · change limitingEnergy _ _ (fun point => potential.val point -
        harmonicInterpolation rule configuration coherent resistance positive compatible minimizer initial potential.val point) ≤ 0
      rw [residualIdentity]
      linarith
    · exact limitingEnergy_nonnegative _ _ _ residual.property
  let anchor : RetainedSkeletonVertex (rule.generation initial).network (configuration initial) :=
    ⟨(rule.generation initial).network.source, SimpleGraph.Reachable.refl _⟩
  have anchorZero : residual.val
      (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial anchor) = 0 := by
    change potential.val _ - harmonicInterpolation rule configuration coherent resistance positive compatible minimizer
      initial potential.val _ = 0
    rw [harmonicInterpolation_boundary, sub_self]
  funext point
  have oscillation := skeleton_finite_energy_resistance_bound rule configuration coherent resistance positive compatible
    residual.val residual.property point
    (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial anchor)
  rw [residualZero, mul_zero, anchorZero, sub_zero] at oscillation
  have valueZero : residual.val point = 0 := sq_eq_zero_iff.mp (le_antisymm oscillation (sq_nonneg _))
  exact sub_eq_zero.mp valueZero

end
end IGSIII34.Diffusion

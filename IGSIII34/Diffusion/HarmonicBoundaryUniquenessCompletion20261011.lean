import IGSIII34.Diffusion.HarmonicTraceIdentificationCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

variable (rule : Rule)
  (configuration : ∀ depth, Configuration (rule.generation depth).edges)
  (coherent : configurationSequenceCoherent rule configuration)
  (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
  (positive : ∀ depth edge, 0 < resistance depth edge)
  (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
    ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
    pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)
  (minimizer : ∀ depth (boundary : Fin (rule.generation depth).vertices → ℝ),
    ∃ potential : Fin (rule.generation (depth + 1)).vertices → ℝ,
      (∀ vertex, ((rule.generation depth).network.openGraph (configuration depth)).Reachable
        (rule.generation depth).network.source vertex → potential (rule.generationOldVertex depth vertex) = boundary vertex) ∧
      sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
        (resistance (depth + 1)) potential =
      sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth) boundary)
  (sourceEnergyLe : ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
    sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth)
      (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
    sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) potential)

include sourceEnergyLe in
/-- A candidate with the prescribed retained coarse boundary and no more
than its exact trace energy is the genuine harmonic tower function.
Unretained artificial boundary values play no part in uniqueness. -/
theorem harmonicTowerFunction_unique_boundary_completion20261011
    (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (candidate : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive))
    (boundaryMatches : ∀ vertex : RetainedSkeletonVertex (rule.generation initial).network (configuration initial),
      candidate.val (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) = boundary vertex.val)
    (energyUpper : limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) candidate.val ≤
      sourceComponentEnergy (network (rule.generation initial).network (configuration initial)) (resistance initial) boundary) :
    candidate.val = harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary := by
  have harmonicFinite := harmonicTowerFunction_finite rule configuration coherent resistance positive compatible minimizer
    sourceEnergyLe initial boundary
  let residual : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive) :=
    ⟨fun point => candidate.val point - harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary point,
      (energyDomain _ _ _).sub_mem candidate.property harmonicFinite⟩
  have boundaryZero (vertex : RetainedSkeletonVertex (rule.generation initial).network (configuration initial)) :
      residual.val (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) = 0 := by
    change candidate.val _ - harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary _ = 0
    rw [boundaryMatches, harmonicTowerFunction_boundary, sub_self]
  have orthogonal := harmonicTowerFunction_orthogonal rule configuration coherent resistance positive compatible minimizer sourceEnergyLe
    initial boundary residual boundaryZero
  have sumIdentity := limitingEnergy_add_identity
    (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
    (skeletonEnergyConductance rule configuration resistance)
    (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary) residual.val
  have sumValues : (fun point => harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary point +
      residual.val point) = candidate.val := by funext point; dsimp [residual]; ring
  rw [sumValues] at sumIdentity
  change limitingPairing _ _ (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary) residual.val = 0 at orthogonal
  rw [orthogonal, mul_zero, add_zero] at sumIdentity
  have harmonicEnergy := harmonicTowerFunction_limiting_energy rule configuration coherent resistance positive compatible minimizer sourceEnergyLe initial boundary
  have residualZero : limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) residual.val = 0 := by
    apply le_antisymm
    · linarith [harmonicEnergy]
    · exact limitingEnergy_nonnegative _ _ _ residual.property
  let anchor : RetainedSkeletonVertex (rule.generation initial).network (configuration initial) :=
    ⟨(rule.generation initial).network.source, SimpleGraph.Reachable.refl _⟩
  funext point
  have oscillation := skeleton_finite_energy_resistance_bound rule configuration coherent resistance positive compatible
    residual.val residual.property point (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial anchor)
  rw [residualZero, mul_zero, boundaryZero, sub_zero] at oscillation
  have valueZero : residual.val point = 0 := sq_eq_zero_iff.mp (le_antisymm oscillation (sq_nonneg _))
  exact sub_eq_zero.mp valueZero

end
end IGSIII34.Diffusion

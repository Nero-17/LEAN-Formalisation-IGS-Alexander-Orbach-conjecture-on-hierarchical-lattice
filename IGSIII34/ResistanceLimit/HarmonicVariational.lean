import IGSIII34.ResistanceLimit.HarmonicTower

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
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
theorem harmonicTowerFunction_minimal (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ)
    (competitor : energyDomain (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive))
    (values : ∀ vertex : RetainedSkeletonVertex (rule.generation initial).network (configuration initial),
      competitor.val (electricalSkeletonVertex rule configuration coherent resistance positive compatible initial vertex) =
        boundary vertex.val) :
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial boundary) ≤
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) competitor.val := by
  have traceIdentity : traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) initial competitor.val =
      sourceComponentEnergy (network (rule.generation initial).network (configuration initial))
        (resistance initial) boundary := by
    rw [skeleton_traceEnergy_eq_source_energy]
    apply sourceComponentEnergy_congr_retained
    intro vertex retained
    have retained' : ((rule.generation initial).network.openGraph (configuration initial)).Reachable
        (rule.generation initial).network.source vertex := by
      rw [graph_eq_openGraph] at retained
      exact retained
    exact (congrArg competitor.val
      (electricalSkeletonPoint_retained rule configuration coherent resistance positive compatible initial
        ⟨vertex, retained'⟩)).trans (values ⟨vertex, retained'⟩)
  exact (harmonicTowerFunction_limiting_energy rule configuration coherent resistance positive compatible minimizer
    sourceEnergyLe initial boundary).le.trans (traceIdentity.symm.le.trans
      (traceEnergy_le_limitingEnergy _ _ _ competitor.property initial))

include sourceEnergyLe in
theorem harmonic_interpolation_energy (initial : ℕ)
    (potential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ) :
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer initial
        (fun vertex => potential (electricalSkeletonPoint rule configuration coherent resistance positive compatible initial vertex))) =
    traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) initial potential :=
  (harmonicTowerFunction_limiting_energy rule configuration coherent resistance positive compatible minimizer
    sourceEnergyLe initial _).trans (skeleton_traceEnergy_eq_source_energy rule configuration coherent resistance positive compatible
      initial potential).symm

end
end IGSIII34.ResistanceLimit

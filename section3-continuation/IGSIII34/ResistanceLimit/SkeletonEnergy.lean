import IGSIII34.ResistanceLimit.ElectricalSkeleton
import IGSIII34.ResistanceLimit.SourceEnergy
import IGSIII34.ResistanceLimit.LimitEnergy

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

def electricalSkeletonVertex (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    ElectricalSkeleton rule configuration coherent resistance positive compatible := ⟦⟨depth, vertex⟩⟧

theorem electricalSkeletonVertex_distance (depth : ℕ)
    (first last : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    dist (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth first)
      (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth last) =
      pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first.val last.val := by
  exact (UniformSpace.Completion.coe_isometry.dist_eq
    (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth first)
    (electricalSkeletonVertex rule configuration coherent resistance positive compatible depth last)).symm.trans
      (electricalVertex_distance rule configuration coherent resistance positive compatible depth first last)

def electricalSkeletonPoint (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    ElectricalSkeleton rule configuration coherent resistance positive compatible :=
  if retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source vertex then
    electricalSkeletonVertex rule configuration coherent resistance positive compatible depth ⟨vertex, retained⟩
  else electricalSkeletonVertex rule configuration coherent resistance positive compatible depth
    ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩

theorem electricalSkeletonVertex_old (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex =
      electricalSkeletonVertex rule configuration coherent resistance positive compatible (depth + 1)
        (retainedOldVertexEmbedding rule configuration coherent depth vertex) := by
  have persistent := DirectLimit.mk_apply
    (f := Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) depth (depth + 1) vertex (Nat.le_succ depth)
  simpa only [electricalSkeletonVertex, Universality.Geometry.IsometricSequence.transition,
    Function.Embedding.coeFn_mk, Nat.leRecOn_succ'] using persistent.symm

theorem electricalSkeletonPoint_old (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    electricalSkeletonPoint rule configuration coherent resistance positive compatible (depth + 1)
        (rule.generationOldVertex depth vertex) =
      electricalSkeletonPoint rule configuration coherent resistance positive compatible depth vertex := by
  have retainedFine : ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
      (rule.generation (depth + 1)).network.source (rule.generationOldVertex depth vertex) ↔
      ((rule.generation depth).network.openGraph (configuration depth)).Reachable
        (rule.generation depth).network.source vertex := by
    change ((rule.generation (depth + 1)).network.openGraph (configuration (depth + 1))).Reachable
      (rule.generationOldVertex depth (rule.generation depth).network.source) (rule.generationOldVertex depth vertex) ↔ _
    rw [rule.generation_reachable_old_iff, coherent depth]
  by_cases retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source vertex
  · simp only [electricalSkeletonPoint, dif_pos retained, dif_pos (retainedFine.mpr retained)]
    exact (electricalSkeletonVertex_old rule configuration coherent resistance positive compatible depth
      ⟨vertex, retained⟩).symm
  · simp only [electricalSkeletonPoint, dif_neg retained, dif_neg (mt retainedFine.mp retained)]
    exact (electricalSkeletonVertex_old rule configuration coherent resistance positive compatible depth
      ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩).symm

theorem electricalSkeletonPoint_retained (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    electricalSkeletonPoint rule configuration coherent resistance positive compatible depth vertex.val =
      electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex := by
  simp only [electricalSkeletonPoint, dif_pos vertex.property]
  congr 1

def skeletonEnergyEndpoint (depth : ℕ)
    (edge : {edge : Fin (rule.generation depth).edges // configuration depth edge = true}) :
    ElectricalSkeleton rule configuration coherent resistance positive compatible ×
      ElectricalSkeleton rule configuration coherent resistance positive compatible :=
  (electricalSkeletonPoint rule configuration coherent resistance positive compatible depth
      ((rule.generation depth).network.endpoint edge.val).1,
    electricalSkeletonPoint rule configuration coherent resistance positive compatible depth
      ((rule.generation depth).network.endpoint edge.val).2)

def skeletonEnergyConductance (depth : ℕ)
    (edge : {edge : Fin (rule.generation depth).edges // configuration depth edge = true}) : ℝ :=
  if ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source ((rule.generation depth).network.endpoint edge.val).1
    then (resistance depth edge)⁻¹ else 0

include positive in
theorem skeletonEnergyConductance_nonnegative (depth : ℕ)
    (edge : {edge : Fin (rule.generation depth).edges // configuration depth edge = true}) :
    0 ≤ skeletonEnergyConductance rule configuration resistance depth edge := by
  unfold skeletonEnergyConductance
  split_ifs
  · exact (inv_pos.mpr (positive depth edge)).le
  · exact le_rfl

include positive in
theorem skeletonEnergyConductance_positive (depth : ℕ)
    (edge : {edge : Fin (rule.generation depth).edges // configuration depth edge = true})
    (retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source ((rule.generation depth).network.endpoint edge.val).1) :
    0 < skeletonEnergyConductance rule configuration resistance depth edge := by
  rw [skeletonEnergyConductance, if_pos retained]
  exact inv_pos.mpr (positive depth edge)

theorem skeleton_traceEnergy_eq_source_energy (depth : ℕ)
    (potential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ) :
    traceEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) depth potential =
    sourceComponentEnergy (network (rule.generation depth).network (configuration depth))
      (resistance depth) (fun vertex => potential
        (electricalSkeletonPoint rule configuration coherent resistance positive compatible depth vertex)) := by
  unfold traceEnergy sourceComponentEnergy
  rw [graph_eq_openGraph]
  unfold finiteEnergy skeletonEnergyEndpoint skeletonEnergyConductance
  simp only [network]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (rule.generation depth).network.source ((rule.generation depth).network.endpoint edge.val).1
  · simp only [if_pos retained]
  · simp only [if_neg retained]

theorem skeleton_traceEnergy_monotone
    (sourceEnergyLe : ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
      sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth)
        (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
      sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
        (resistance (depth + 1)) potential)
    (potential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ) :
    Monotone (fun depth => traceEnergy
      (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) depth potential) := by
  apply monotone_nat_of_le_succ
  intro depth
  simp only [skeleton_traceEnergy_eq_source_energy]
  have bound := sourceEnergyLe depth (fun vertex => potential
    (electricalSkeletonPoint rule configuration coherent resistance positive compatible (depth + 1) vertex))
  simpa only [electricalSkeletonPoint_old] using bound

theorem skeleton_finite_energy_resistance_bound
    (potential : ElectricalSkeleton rule configuration coherent resistance positive compatible → ℝ)
    (finite : potential ∈ energyDomain
      (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance)
      (skeletonEnergyConductance_nonnegative rule configuration resistance positive)) :
    ∀ first last, (potential first - potential last) ^ 2 ≤ dist first last *
      limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance) potential := by
  intro first last
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) (fun depth first last => ?_) first last
  change (potential (electricalSkeletonVertex _ _ _ _ _ _ depth first) -
    potential (electricalSkeletonVertex _ _ _ _ _ _ depth last)) ^ 2 ≤
    dist (electricalSkeletonVertex _ _ _ _ _ _ depth first)
      (electricalSkeletonVertex _ _ _ _ _ _ depth last) *
    limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
      (skeletonEnergyConductance rule configuration resistance) potential
  rw [electricalSkeletonVertex_distance]
  have bound := sourceComponentEnergy_resistance_bound
    (network (rule.generation depth).network (configuration depth)) (resistance depth) (positive depth)
    (fun vertex => potential (electricalSkeletonPoint rule configuration coherent resistance positive compatible depth vertex))
    (first := first.val) (last := last.val)
    (by rw [graph_eq_openGraph]; exact first.property)
    (by rw [graph_eq_openGraph]; exact last.property)
  rw [electricalSkeletonPoint_retained, electricalSkeletonPoint_retained] at bound
  refine bound.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [← skeleton_traceEnergy_eq_source_energy]
    exact traceEnergy_le_limitingEnergy _ _ _ finite depth
  · exact pairResistance_nonnegative _ _ (positive depth)
      (by simpa only [graph_eq_openGraph] using first.property.symm.trans last.property)

end
end IGSIII34.ResistanceLimit

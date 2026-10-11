import IGSIII34.Diffusion.RootedElectricalSkeleton
import IGSIII34.ResistanceLimit.SelectedComponentEnergy
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)

def rootedElectricalSkeletonVertex (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible := ⟦⟨depth, vertex⟩⟧

theorem rootedElectricalSkeletonVertex_distance (depth : ℕ)
    (first last : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    dist (rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth first)
      (rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth last) =
      pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first.val last.val := by
  exact (UniformSpace.Completion.coe_isometry.dist_eq
    (rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth first)
    (rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth last)).symm.trans
      (rootedElectricalVertex_distance rule configuration coherent sourceSide resistance positive compatible depth first last)

def rootedElectricalSkeletonPoint (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible :=
  if retained : ((rule.generation depth).network.openGraph (configuration depth)).Reachable
      (plantedVertex (rule.generation depth).network sourceSide) vertex then
    rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth ⟨vertex, retained⟩
  else rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth
    ⟨plantedVertex (rule.generation depth).network sourceSide, SimpleGraph.Reachable.refl _⟩

theorem rootedElectricalSkeletonPoint_retained (depth : ℕ)
    (vertex : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide) :
    rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible depth vertex.val =
      rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth vertex := by
  simp only [rootedElectricalSkeletonPoint, dif_pos vertex.property]
  congr 1

/-- Finite trace energy of the selected intrinsic component alone. -/
def rootedElectricalIntrinsicTraceEnergy (depth : ℕ)
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ) : ℝ :=
  sourceComponentEnergy (sideNetwork (network (rule.generation depth).network (configuration depth)) sourceSide)
    (resistance depth) (fun vertex => potential
      (rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible depth vertex))

/-- Finite local energy means boundedness of the actual local finite traces. -/
def rootedElectricalIntrinsicFiniteEnergy
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ) : Prop :=
  BddAbove (Set.range (fun depth => rootedElectricalIntrinsicTraceEnergy rule configuration coherent sourceSide resistance positive compatible depth potential))

def rootedElectricalIntrinsicEnergy
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ) : ℝ :=
  ⨆ depth, rootedElectricalIntrinsicTraceEnergy rule configuration coherent sourceSide resistance positive compatible depth potential

theorem rootedElectricalIntrinsicTraceEnergy_le
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (finite : rootedElectricalIntrinsicFiniteEnergy rule configuration coherent sourceSide resistance positive compatible potential)
    (depth : ℕ) :
    rootedElectricalIntrinsicTraceEnergy rule configuration coherent sourceSide resistance positive compatible depth potential ≤
      rootedElectricalIntrinsicEnergy rule configuration coherent sourceSide resistance positive compatible potential := le_ciSup finite depth

theorem rootedElectricalIntrinsicEnergy_nonnegative
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (finite : rootedElectricalIntrinsicFiniteEnergy rule configuration coherent sourceSide resistance positive compatible potential) :
    0 ≤ rootedElectricalIntrinsicEnergy rule configuration coherent sourceSide resistance positive compatible potential :=
  (sourceComponentEnergy_nonnegative _ _ (positive 0) _).trans
    (rootedElectricalIntrinsicTraceEnergy_le rule configuration coherent sourceSide resistance positive compatible potential finite 0)

theorem rootedElectricalIntrinsicEnergy_resistance_bound
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (finite : rootedElectricalIntrinsicFiniteEnergy rule configuration coherent sourceSide resistance positive compatible potential) :
    ∀ first last, (potential first - potential last) ^ 2 ≤ dist first last *
      rootedElectricalIntrinsicEnergy rule configuration coherent sourceSide resistance positive compatible potential := by
  intro first last
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) (fun depth first last => ?_) first last
  change (potential (rootedElectricalSkeletonVertex _ _ _ _ _ _ _ depth first) -
    potential (rootedElectricalSkeletonVertex _ _ _ _ _ _ _ depth last)) ^ 2 ≤
    dist (rootedElectricalSkeletonVertex _ _ _ _ _ _ _ depth first)
      (rootedElectricalSkeletonVertex _ _ _ _ _ _ _ depth last) *
    rootedElectricalIntrinsicEnergy rule configuration coherent sourceSide resistance positive compatible potential
  rw [rootedElectricalSkeletonVertex_distance]
  have bound := sourceComponentEnergy_resistance_bound
    (sideNetwork (network (rule.generation depth).network (configuration depth)) sourceSide) (resistance depth) (positive depth)
    (fun vertex => potential (rootedElectricalSkeletonPoint rule configuration coherent sourceSide resistance positive compatible depth vertex))
    (first := first.val) (last := last.val)
    (by rw [sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source]; exact first.property)
    (by rw [sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source]; exact last.property)
  rw [rootedElectricalSkeletonPoint_retained, rootedElectricalSkeletonPoint_retained, pairResistance_sideNetwork] at bound
  refine bound.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · exact rootedElectricalIntrinsicTraceEnergy_le rule configuration coherent sourceSide resistance positive compatible potential finite depth
  · exact pairResistance_nonnegative _ _ (positive depth)
      (by simpa only [graph_eq_openGraph] using first.property.symm.trans last.property)

theorem rootedElectricalIntrinsicFiniteEnergy_uniformContinuous
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (finite : rootedElectricalIntrinsicFiniteEnergy rule configuration coherent sourceSide resistance positive compatible potential) :
    UniformContinuous potential := by
  have energyNonnegative := rootedElectricalIntrinsicEnergy_nonnegative rule configuration coherent sourceSide resistance positive compatible potential finite
  apply Metric.uniformContinuous_iff.mpr
  intro epsilon epsilonPositive
  have denominatorPositive : 0 < rootedElectricalIntrinsicEnergy rule configuration coherent sourceSide resistance positive compatible potential + 1 := by linarith
  refine ⟨epsilon ^ 2 / (rootedElectricalIntrinsicEnergy rule configuration coherent sourceSide resistance positive compatible potential + 1),
    div_pos (sq_pos_of_pos epsilonPositive) denominatorPositive, ?_⟩
  intro first last close
  have bound := rootedElectricalIntrinsicEnergy_resistance_bound rule configuration coherent sourceSide resistance positive compatible potential finite first last
  have multiplied := mul_lt_mul_of_pos_right close denominatorPositive
  rw [div_mul_cancel₀ _ denominatorPositive.ne'] at multiplied
  rw [Real.dist_eq]
  nlinarith [sq_abs (potential first - potential last), abs_nonneg (potential first - potential last), dist_nonneg (x := first) (y := last)]

def rootedElectricalIntrinsicCompletionExtension
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ) :
    C(RootedElectricalSpace rule configuration coherent sourceSide resistance positive compatible, ℝ) :=
  ⟨UniformSpace.Completion.extension potential, UniformSpace.Completion.continuous_extension⟩

theorem rootedElectricalIntrinsicCompletionExtension_coe
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (finite : rootedElectricalIntrinsicFiniteEnergy rule configuration coherent sourceSide resistance positive compatible potential)
    (point : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible) :
    rootedElectricalIntrinsicCompletionExtension rule configuration coherent sourceSide resistance positive compatible potential (UniformSpace.Completion.coe' point) = potential point :=
  UniformSpace.Completion.extension_coe
    (rootedElectricalIntrinsicFiniteEnergy_uniformContinuous rule configuration coherent sourceSide resistance positive compatible potential finite) point

/-- The intrinsic resistance inequality on the genuinely completed selected
component uses its local energy, without substitution of the global energy. -/
theorem rootedElectricalIntrinsicCompletionExtension_resistance_bound
    (potential : RootedElectricalSkeleton rule configuration coherent sourceSide resistance positive compatible → ℝ)
    (finite : rootedElectricalIntrinsicFiniteEnergy rule configuration coherent sourceSide resistance positive compatible potential)
    (first last : RootedElectricalSpace rule configuration coherent sourceSide resistance positive compatible) :
    (rootedElectricalIntrinsicCompletionExtension rule configuration coherent sourceSide resistance positive compatible potential first -
      rootedElectricalIntrinsicCompletionExtension rule configuration coherent sourceSide resistance positive compatible potential last) ^ 2 ≤
    dist first last * rootedElectricalIntrinsicEnergy rule configuration coherent sourceSide resistance positive compatible potential := by
  refine UniformSpace.Completion.induction_on₂ first last ?_ ?_
  · apply isClosed_le
    · exact (((rootedElectricalIntrinsicCompletionExtension rule configuration coherent sourceSide resistance positive compatible potential).continuous.comp continuous_fst).sub
        ((rootedElectricalIntrinsicCompletionExtension rule configuration coherent sourceSide resistance positive compatible potential).continuous.comp continuous_snd)).pow 2
    · exact continuous_dist.mul continuous_const
  · intro first last
    rw [rootedElectricalIntrinsicCompletionExtension_coe rule configuration coherent sourceSide resistance positive compatible potential finite,
      rootedElectricalIntrinsicCompletionExtension_coe rule configuration coherent sourceSide resistance positive compatible potential finite,
      UniformSpace.Completion.dist_eq]
    exact rootedElectricalIntrinsicEnergy_resistance_bound rule configuration coherent sourceSide resistance positive compatible potential finite first last

end
end IGSIII34.Diffusion

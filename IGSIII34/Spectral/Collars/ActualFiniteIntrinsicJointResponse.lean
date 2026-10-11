import IGSIII34.Diffusion.IntrinsicJointGHPPathTransport
import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCanonicalPath
import IGSIII34.ResistanceLimit.ActualCommonChemicalHausdorff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped _root_.Topology NNReal

variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

def actualFiniteIntrinsicJointMark
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true) (side : Bool) :
    ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth :=
  ⟨plantedVertex (rule.generation depth).network side, by
    rw [configurationAtDepth_self]
    cases side with
    | false => exact ((rule.generation depth).network.crosses_eq_true configuration).mp crossing
    | true => exact SimpleGraph.Reachable.refl _⟩

def actualFiniteIntrinsicJointMass
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true) (counting : Bool) :
    ProbabilityMeasure (ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) := by
  letI := clusterEdge_nonempty (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
    (by simpa only [configurationAtDepth_self] using crossing)
  exact if counting then ⟨uniformOn Set.univ, inferInstance⟩ else
    ⟨degreeMeasure (clusterRetainedEndpoint (rule.generation depth).network
      (configurationAtDepth rule depth configuration depth)), inferInstance⟩

def actualFiniteIntrinsicJointState
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true) :
    JointMeasuredMarkedState (ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) :=
  (continuousNonemptyCompactRange id continuous_id,
    actualFiniteIntrinsicJointMark rule scale scalePositive depth configuration crossing,
    actualFiniteIntrinsicJointMass rule scale scalePositive depth configuration crossing)

/-- The full intrinsic GHP/whole-path test response depends only on the
actual finite configuration and selected starting vertex. It does not use
an environment-dependent choice of common ambient. -/
def actualFiniteIntrinsicJointResponse (test : IntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) : ℝ := by
  classical
  if crossing : (rule.generation depth).network.crosses input.1 = true then
    if positive : 0 < clock input.1 then
      exact ∫ path, test.value _ (actualFiniteIntrinsicJointState rule scale scalePositive depth input.1 crossing) path
        ∂(actualFiniteAnnealedCanonicalPathLaw rule scale scalePositive depth input.1 crossing
          input.2 (clock input.1) positive kind : Measure _)
    else exact 0
  else exact 0

theorem actualFiniteIntrinsicJointResponse_bound (test : IntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    ‖actualFiniteIntrinsicJointResponse rule scale scalePositive depth test clock kind input‖ ≤ test.bound := by
  classical
  unfold actualFiniteIntrinsicJointResponse
  split_ifs
  · exact intrinsic_joint_test_integral_bound test _ _
  all_goals simpa only [norm_zero] using test.bound.coe_nonneg

/-- This is the exact response of the original finite walk in every true
isometric placement, with the actual geometry, both masses and marks. -/
theorem actualFiniteIntrinsicJointResponse_isometric_placement
    {Ambient : Type} [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (test : IntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (initial : Fin (rule.generation depth).vertices) (clockPositive : 0 < clock configuration)
    (placement : ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth → Ambient)
    (isometry : Isometry placement) :
    actualFiniteIntrinsicJointResponse rule scale scalePositive depth test clock kind (configuration, initial) =
      ∫ path, test.value Ambient (jointMeasuredMarkedStateMap placement isometry.continuous
        (actualFiniteIntrinsicJointState rule scale scalePositive depth configuration crossing)) path
      ∂(actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth configuration crossing initial
        (clock configuration) clockPositive kind placement : Measure _) := by
  classical
  unfold actualFiniteIntrinsicJointResponse
  simp only [dif_pos crossing, dif_pos clockPositive]
  rw [actualFiniteAnnealedPlacedPathLaw_eq_canonical_map rule scale scalePositive depth configuration crossing
    initial (clock configuration) clockPositive kind placement isometry.continuous]
  exact (intrinsic_joint_test_integral_isometric_transport test placement isometry _ _).symm

end
end IGSIII34.Spectral

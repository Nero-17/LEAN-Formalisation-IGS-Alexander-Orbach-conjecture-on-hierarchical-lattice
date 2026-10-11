import IGSIII34.Diffusion.IntegerIntrinsicJointGHPPathTransport
import IGSIII34.Spectral.Collars.ActualFiniteIntrinsicJointResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped _root_.Topology NNReal

variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

/-- The full intrinsic GHP/whole-path test response depends only on the
actual finite configuration and selected starting vertex. It does not use
an environment-dependent choice of common ambient. -/
def actualFiniteIntegerIntrinsicJointResponse (test : IntegerIntrinsicJointGHPPathTest)
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

theorem actualFiniteIntegerIntrinsicJointResponse_bound (test : IntegerIntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    ‖actualFiniteIntegerIntrinsicJointResponse rule scale scalePositive depth test clock kind input‖ ≤ test.bound := by
  classical
  unfold actualFiniteIntegerIntrinsicJointResponse
  split_ifs
  · exact integer_intrinsic_joint_test_integral_bound test _ _
  all_goals simpa only [norm_zero] using test.bound.coe_nonneg

/-- This is the exact response of the original finite walk in every true
isometric placement, with the actual geometry, both masses and marks. -/
theorem actualFiniteIntegerIntrinsicJointResponse_isometric_placement
    {Ambient : Type} [MetricSpace Ambient] [CompactSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (test : IntegerIntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (initial : Fin (rule.generation depth).vertices) (clockPositive : 0 < clock configuration)
    (placement : ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth → Ambient)
    (isometry : Isometry placement) :
    actualFiniteIntegerIntrinsicJointResponse rule scale scalePositive depth test clock kind (configuration, initial) =
      ∫ path, test.value Ambient (jointMeasuredMarkedStateMap placement isometry.continuous
        (actualFiniteIntrinsicJointState rule scale scalePositive depth configuration crossing)) path
      ∂(actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth configuration crossing initial
        (clock configuration) clockPositive kind placement : Measure _) := by
  classical
  unfold actualFiniteIntegerIntrinsicJointResponse
  simp only [dif_pos crossing, dif_pos clockPositive]
  rw [actualFiniteAnnealedPlacedPathLaw_eq_canonical_map rule scale scalePositive depth configuration crossing
    initial (clock configuration) clockPositive kind placement isometry.continuous]
  exact (integer_intrinsic_joint_test_integral_isometric_transport test placement isometry _ _).symm

end
end IGSIII34.Spectral

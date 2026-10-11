import IGSIII34.Forms.ActualEnergyHilbert
import IGSIII34.Spectral.HilbertEvaluation

/-! Bounded completed-point evaluation on the actual anchored energy Hilbert
space. This supplies the Riesz functional for actual finite-energy functions;
the anchored norm is not identified with an L² resolvent norm in this file. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory
open scoped Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)

theorem actual_anchored_norm_square
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :
    letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    ‖potential‖ ^ 2 = limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
        potential.val anchor ^ 2 := by
  have square := anchored_norm_square
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
    anchor potential
  simpa only [anchoredSquare, pow_two] using square

theorem actual_completion_evaluation_bound
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    ∀ potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks,
      ‖actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point‖ ≤
        Real.sqrt (2 * (dist point anchor + 1)) * ‖potential‖ := by
  letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
  intro potential
  have comparison := actualEnergyExtension_resistance rule p positive belowOne fixedPoint growth value
    growthPositive marks potential point anchor
  have anchorEquality : actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value
      growthPositive marks potential anchor = potential.val anchor :=
    completionExtension_coe
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
      potential anchor
  rw [anchorEquality] at comparison
  have square := actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive
    marks anchor potential
  have energyNonnegative := limitingEnergy_nonnegative
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    potential.property
  have energyBound : limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val ≤ ‖potential‖ ^ 2 := by
    nlinarith [sq_nonneg (potential.val anchor)]
  have productBound := mul_le_mul_of_nonneg_left energyBound (dist_nonneg (x := point) (y := anchor))
  have sqrtIdentity : Real.sqrt (2 * (dist point anchor + 1)) ^ 2 = 2 * (dist point anchor + 1) :=
    Real.sq_sqrt (by positivity)
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [sq_abs, mul_pow, sqrtIdentity]
  have anchorBound : potential.val anchor ^ 2 ≤ ‖potential‖ ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value
    growthPositive marks potential point - 2 * potential.val anchor)]

def actualCompletionEvaluation
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    letI : TopologicalSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
      (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
    StrongDual ℝ (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) := by
  letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
  letI : TopologicalSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
    (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
  let evaluation : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks →ₗ[ℝ] ℝ :=
    { toFun := fun potential => actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value
        growthPositive marks potential point
      map_add' := by intro first second; simp
      map_smul' := by intro scalar potential; simp }
  exact evaluation.mkContinuous (Real.sqrt (2 * (dist point anchor + 1)))
    (actual_completion_evaluation_bound rule p positive belowOne fixedPoint growth value growthPositive marks anchor point)

theorem actual_completion_evaluation_variational
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    letI : UniformSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
      (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
    letI : TopologicalSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
      (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
    letI := actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    sSup (Set.range (fun potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks =>
      (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point) ^ 2 /
        ‖potential‖ ^ 2)) =
      ‖actualCompletionEvaluation rule p positive belowOne fixedPoint growth value growthPositive marks anchor point‖ ^ 2 := by
  letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
  letI : UniformSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
    (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
  letI : TopologicalSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
    (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
  letI := actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
  letI := actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
  exact evaluation_variational_identity
    (actualCompletionEvaluation rule p positive belowOne fixedPoint growth value growthPositive marks anchor point)

end
end IGSIII34.Spectral

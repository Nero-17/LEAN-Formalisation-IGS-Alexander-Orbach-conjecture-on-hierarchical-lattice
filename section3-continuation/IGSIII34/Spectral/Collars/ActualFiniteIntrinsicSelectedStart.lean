import IGSIII34.Spectral.Collars.ActualAnnealedStartingConvergence
import IGSIII34.Spectral.Collars.ActualFiniteIntrinsicJointResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.ResistanceLimit IGSIII34.Diffusion MeasureTheory

theorem actualFiniteAnnealedInitialVertex_selected_identity
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : Fin (rule.generation depth).vertices) :
    actualFiniteAnnealedInitialVertex rule scale scalePositive depth (stationaryConfiguration rule marks depth)
      (actualAnnealedSelectedVertex rule marks depth initial).val =
    actualFiniteAnnealedInitialVertex rule scale scalePositive depth (stationaryConfiguration rule marks depth) initial := by
  classical
  unfold actualAnnealedSelectedVertex actualFiniteAnnealedInitialVertex
  split_ifs <;> apply Subtype.ext <;> rfl

theorem actualFiniteIntrinsicJointResponse_selected_identity
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (test : IntrinsicJointGHPPathTest)
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : Fin (rule.generation depth).vertices) :
    actualFiniteIntrinsicJointResponse rule scale scalePositive depth test clock kind
      (stationaryConfiguration rule marks depth, (actualAnnealedSelectedVertex rule marks depth initial).val) =
    actualFiniteIntrinsicJointResponse rule scale scalePositive depth test clock kind
      (stationaryConfiguration rule marks depth, initial) := by
  classical
  unfold actualFiniteIntrinsicJointResponse
  split_ifs
  · unfold actualFiniteAnnealedCanonicalPathLaw
    simp only [actualFiniteAnnealedInitialVertex_selected_identity rule marks scale scalePositive depth initial]
  all_goals rfl

end
end IGSIII34.Spectral

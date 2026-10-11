import IGSIII34.Spectral.Collars.ActualFiniteAnnealedProfilePaths
import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode
import IGSIII34.Diffusion.CountableDistanceProfileCadlagWeak

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4600000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII34.Spectral IGSIII34.Diffusion MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (classicalRule : rule.Classical)
  (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
  (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
  (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
  (scale : ℝ) (scalePositive : 0 < scale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))


include crossing in
/-- Literal full finite paths in the compact spatial profile inherit the
actual same-carrier quenched path limit. The original finite metric and
original birth embeddings supply the spatial approximation. -/
theorem actualFiniteAnnealedCompactProfile_uniform
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ vertex,
      dist (actualFiniteAnnealedCompactProfile rule scale scalePositive depth
        (markedGenerationConfiguration rule marks depth [] true) vertex)
        (distanceProfilePoint
          (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
            coherent scale scalePositive lengths nonnegative positive childConvergence)
          (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
            coherent scale scalePositive lengths nonnegative positive childConvergence depth
            (actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              scale scalePositive depth vertex))) < tolerance := by
  apply countableDistanceProfile_uniform_of_coordinate_uniform (tolerancePositive := tolerancePositive)
  intro label coordinateTolerance coordinatePositive
  filter_upwards [actualFiniteAnnealedDistanceProfile_uniform rule classicalRule marks crossing coherent
    scale scalePositive lengths nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne
    radiusBounds label coordinateTolerance coordinatePositive] with depth near
  intro vertex
  change |Real.exp (-actualFiniteAnnealedDistanceProfile rule scale scalePositive depth
      (markedGenerationConfiguration rule marks depth [] true) vertex label) -
    Real.exp (-dist (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive lengths nonnegative positive childConvergence depth
      (actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex))
      (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive lengths nonnegative positive childConvergence label))| < coordinateTolerance
  exact (exp_neg_distance_difference_le dist_nonneg dist_nonneg).trans_lt (near vertex)

end
end IGSIII34.ResistanceLimit

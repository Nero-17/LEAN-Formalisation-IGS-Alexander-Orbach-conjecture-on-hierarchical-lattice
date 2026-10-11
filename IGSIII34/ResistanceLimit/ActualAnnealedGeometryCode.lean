import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCoding
import IGSIII34.ResistanceLimit.ActualChemicalBirthDistortionCompletion20261011
import IGSIII.Geometry.ChemicalMetricCodeFaithfulness

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII34.Spectral MeasureTheory Filter
open scoped _root_.Topology

/-- The coding's configuration-at-depth carrier is the original finite
cluster with identical vertex labels and identical normalized metric. -/
def actualAnnealedFiniteVertexEquiv (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ) :
    IsometryEquiv (ActualFiniteCluster rule (configurationAtDepth rule depth (configuration depth)) scale scalePositive depth)
      (ActualFiniteCluster rule configuration scale scalePositive depth) where
  toEquiv := Equiv.subtypeEquivRight (fun vertex => by rw [configurationAtDepth_self])
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro first last
    change (((rule.generation depth).network.openGraph (configuration depth)).dist first.val last.val : ℝ) / scale ^ (depth + 1) =
      (((rule.generation depth).network.openGraph (configurationAtDepth rule depth (configuration depth) depth)).dist first.val last.val : ℝ) / scale ^ (depth + 1)
    exact congrArg (fun state : Configuration (rule.generation depth).edges =>
      (((rule.generation depth).network.openGraph state).dist first.val last.val : ℝ) / scale ^ (depth + 1))
      (configurationAtDepth_self rule depth (configuration depth)).symm

theorem actualAnnealedFiniteVertexEquiv_val (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (vertex : ActualFiniteCluster rule (configurationAtDepth rule depth (configuration depth)) scale scalePositive depth) :
    (actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth vertex).val = vertex.val := rfl

theorem actualFiniteAnnealedBirthProjection_persistent (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (label : ActualAnnealedBirthLabels rule) (bound : label.1 ≤ depth) :
    actualAnnealedFiniteVertexEquiv rule configuration scale scalePositive depth
      (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (configuration depth) label) =
    retainedFiniteVertexEmbedding rule configuration coherent scale scalePositive label.1 depth bound
      (chemicalRetainedLabelVertex rule configuration label) := by
  classical
  have sourceIdentity : persistentVertexEmbedding rule label.1 depth bound (rule.generation label.1).network.source =
      (rule.generation depth).network.source :=
    persistentVertexEmbedding_planted rule label.1 depth bound true
  have reachable := persistentVertexEmbedding_reachable_iff rule configuration coherent label.1 depth bound
    (rule.generation label.1).network.source label.2
  rw [sourceIdentity] at reachable
  by_cases retained : ((rule.generation label.1).network.openGraph (configuration label.1)).Reachable
      (rule.generation label.1).network.source label.2
  · have current := reachable.mpr retained
    apply Subtype.ext
    simp only [actualAnnealedFiniteVertexEquiv_val, actualFiniteAnnealedBirthProjection,
      dif_pos bound, dif_pos current, retainedFiniteVertexEmbedding_val, chemicalRetainedLabelVertex, dif_pos retained]
  · have current := fun present => retained (reachable.mp present)
    apply Subtype.ext
    simp only [actualAnnealedFiniteVertexEquiv_val, actualFiniteAnnealedBirthProjection,
      dif_pos bound, dif_neg current, retainedFiniteVertexEmbedding_val, chemicalRetainedLabelVertex, dif_neg retained]
    exact sourceIdentity.symm

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

theorem actualFiniteAnnealedBirthProjection_chemical (depth : ℕ)
    (label : ActualAnnealedBirthLabels rule) (bound : label.1 ≤ depth) :
    actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive lengths nonnegative positive childConvergence depth
      (actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth
        (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (markedGenerationConfiguration rule marks depth [] true) label)) =
    actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive lengths nonnegative positive childConvergence label := by
  rw [actualFiniteAnnealedBirthProjection_persistent]
  exact (actualChemicalVertex_persistent rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive lengths nonnegative positive childConvergence label.1 depth bound
    (chemicalRetainedLabelVertex rule (fun depth => markedGenerationConfiguration rule marks depth [] true) label)).symm

include crossing in
/-- Every actual raw distance-to-birth profile is uniformly close over the
whole finite cluster to the corresponding actual completed chemical profile. -/
theorem actualFiniteAnnealedDistanceProfile_uniform
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (label : ActualAnnealedBirthLabels rule) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ vertex,
      |actualFiniteAnnealedDistanceProfile rule scale scalePositive depth
          (markedGenerationConfiguration rule marks depth [] true) vertex label -
        dist (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence depth
          (actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex))
          (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
            coherent scale scalePositive lengths nonnegative positive childConvergence label)| < tolerance := by
  filter_upwards [actual_chemical_birth_uniform_distortion_completion20261011 rule classicalRule marks crossing coherent
    scale scalePositive lengths nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne radiusBounds tolerance tolerancePositive,
    eventually_ge_atTop label.1] with depth distortion bound
  intro vertex
  have estimate := distortion
    (actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex)
    (actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth
      (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (markedGenerationConfiguration rule marks depth [] true) label))
  rw [(actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth).dist_eq,
    actualFiniteAnnealedBirthProjection_chemical rule classicalRule marks coherent scale scalePositive lengths nonnegative positive childConvergence depth label bound] at estimate
  exact estimate

end
end IGSIII34.ResistanceLimit

import IGSIII34.ResistanceLimit.ActualChemicalBirthDistortionCompletion
import IGSIII34.Topology.CommonProjectionMetricRealisationCompletion
import IGSIII.Geometry.ActualChemicalNets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5800000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

/-- The actual normalized finite chemical graphs and their constructed
chemical completion have a single compact complete common realization
by isometric embeddings. Every finite vertex is uniformly close to its
actual chemical birth image in that realization. -/
theorem exists_actual_chemical_common_isometric_realisation_completion
    (rule : Rule) (classicalRule : rule.Classical)
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
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length) :
    ∃ (Ambient : Type) (ambientMetric : MetricSpace Ambient),
      letI := ambientMetric
      CompleteSpace Ambient ∧ CompactSpace Ambient ∧
      ∃ target : ActualChemicalSpace rule classicalRule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
        nonnegative positive childConvergence → Ambient,
        Isometry target ∧
      ∃ sources : ∀ depth, ActualFiniteCluster rule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth → Ambient,
        (∀ depth, Isometry (sources depth)) ∧
        ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ point,
          dist (sources depth point) (target (actualChemicalVertex rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
            nonnegative positive childConvergence depth point)) < tolerance := by
  letI : ∀ depth, Fintype (ActualFiniteCluster rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth) :=
    fun depth => Fintype.ofFinite _
  letI : CompactSpace (ActualChemicalSpace rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
      nonnegative positive childConvergence) :=
    actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
      nonnegative positive childConvergence marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne
      coefficientNonnegative radiusBounds
  letI : Nonempty (ActualChemicalSpace rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
      nonnegative positive childConvergence) :=
    ⟨actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive lengths nonnegative positive childConvergence 0
      ⟨(rule.generation 0).network.source, SimpleGraph.Reachable.refl _⟩⟩
  exact IGSIII34.Topology.exists_common_isometric_realisation_of_uniform_projection_distortion_completion
    (fun depth => ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive depth)
    (fun depth => actualChemicalVertex rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
      nonnegative positive childConvergence depth)
    (actual_chemical_birth_uniform_distortion_completion rule classicalRule marks crossing coherent
      scale scalePositive lengths nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne radiusBounds)

end
end IGSIII34.ResistanceLimit

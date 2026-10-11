import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode
import Mathlib.Topology.MetricSpace.Closeds

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII34.Spectral MeasureTheory Filter TopologicalSpace
open scoped _root_.Topology

def continuousNonemptyCompactRange {Source Ambient : Type*} [TopologicalSpace Source] [CompactSpace Source] [Nonempty Source]
    [TopologicalSpace Ambient] (mapping : Source → Ambient) (continuous : Continuous mapping) : NonemptyCompacts Ambient :=
  ⟨⟨Set.range mapping, isCompact_range continuous⟩, Set.range_nonempty _⟩
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

variable {Ambient : Type*} [MetricSpace Ambient]
  (target : ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive lengths nonnegative positive childConvergence → Ambient)
  (targetIsometry : Isometry target)
  (sources : ∀ depth, ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth → Ambient)
  (sourceIsometry : ∀ depth, Isometry (sources depth))
  (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
    dist (sources depth vertex) (target (actualChemicalVertex rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence depth vertex)) < tolerance)

/-- On the SAME prescribed common ambient, the entire original finite
cluster images converge in Hausdorff topology to the actual chemical image. -/
theorem actual_common_chemical_compact_images_tendsto
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length) :
    letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
      marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    Tendsto (fun depth => continuousNonemptyCompactRange (sources depth) (sourceIsometry depth).continuous) atTop
      (𝓝 (continuousNonemptyCompactRange target targetIsometry.continuous)) := by
  letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
    marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  have mesh : Tendsto (fun depth => coefficient * eta ^ (depth + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1)).const_mul coefficient)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  filter_upwards [placementClose (tolerance / 4) (by positivity),
    (tendsto_order.mp mesh).2 (tolerance / 4) (by positivity), eventually_ge_atTop start] with depth close small beyond
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, NonemptyCompacts.dist_eq]
  have bound : Metric.hausdorffDist (Set.range (sources depth)) (Set.range target) ≤ tolerance / 2 := by
    apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
    · rintro _ ⟨vertex, rfl⟩
      refine ⟨target (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive lengths nonnegative positive childConvergence depth vertex), Set.mem_range_self _, ?_⟩
      exact (close vertex).le.trans (by linarith)
    · rintro _ ⟨point, rfl⟩
      obtain ⟨vertex, near⟩ := actualChemicalSpace_near_birth_skeleton rule classicalRule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
        marks (fun _ => rfl) eta coefficient start etaNonnegative coefficientNonnegative radiusBounds depth (by omega) point
      refine ⟨sources depth vertex, Set.mem_range_self _, ?_⟩
      have triangle := dist_triangle (target point)
        (target (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence depth vertex)) (sources depth vertex)
      rw [targetIsometry.dist_eq, dist_comm _ (sources depth vertex)] at triangle
      exact triangle.trans (by linarith [close vertex])
  exact bound.trans_lt (by linarith)

/-- Every fixed planted or born mark converges under the prescribed source
placements. In particular this applies to both ordered planted terminals. -/
theorem actual_common_chemical_born_mark_tendsto (age : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation age).network (markedGenerationConfiguration rule marks age [] true)) :
    Tendsto (fun depth => if bound : age ≤ depth then
      sources depth (retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive age depth bound vertex) else sources depth ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩) atTop
      (𝓝 (target (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive lengths nonnegative positive childConvergence age vertex))) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  filter_upwards [placementClose tolerance tolerancePositive, eventually_ge_atTop age] with depth close bound
  simp only [dif_pos bound]
  have estimate := close (retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive age depth bound vertex)
  rw [← actualChemicalVertex_persistent rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive lengths nonnegative positive childConvergence age depth bound vertex] at estimate
  exact estimate

end
end IGSIII34.ResistanceLimit



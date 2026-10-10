import IGSIII34.Diffusion.ActualDegreeProjection
import IGSIII.Geometry.ExceptionalTransport

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem actual_degree_projection_bound (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool)) (radius : ℝ) (nonnegative : 0 ≤ radius)
    (radiusBound : ∀ word : Fin (age + 1) → (Fin rule.edges × Bool),
      (markedTerminalComponentRadius rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened : ℝ) /
        scale ^ (fine + (age + 1) + 1) ≤ radius) :
    levyProkhorovEDist
      (actualFiniteClusterDegreeMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive (fine + (age + 1)))
      ((edgeComponentWordLaw rule marks crossing fine (age + 1)).map
        (fun word => retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive age (fine + (age + 1)) (by omega)
          (actualComponentRetainedAnchor rule marks crossing age word))) ≤ ENNReal.ofReal radius := by
  classical
  letI := clusterEdge_nonempty (rule.generation (fine + (age + 1))).network _
    (markedGenerationConfiguration_crosses rule marks crossing (fine + (age + 1)) [] true)
  let anchor := fun word => retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive age (fine + (age + 1)) (by omega)
    (actualComponentRetainedAnchor rule marks crossing age word)
  have close edge side : dist
      (halfEndpoint (Vertex := ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        scale scalePositive (fine + (age + 1))) (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _)
        (edge, side)) (anchor (actualComponentEdgeOwnership rule marks crossing fine (age + 1) fallback edge)) ≤ radius :=
    (actualComponentEdgeOwnership_half_distance_le rule marks crossing coherent scale scalePositive fine age fallback edge side).trans
      (radiusBound _)
  have result := degree_projection_bound
    (Vertex := ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (fine + (age + 1)))
    (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _)
    id (actualComponentEdgeOwnership rule marks crossing fine (age + 1) fallback) anchor radius nonnegative
    (fun edge => ⟨by simpa only [halfEndpoint, if_true, id_eq] using close edge true,
      by simpa only [halfEndpoint, Bool.false_eq_true, if_false, id_eq] using close edge false⟩)
  have law := congrArg (fun measure => measure.map anchor) (actual_half_owner_law rule marks crossing fine (age + 1) fallback)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at law
  simp only [Function.comp_def] at law
  rw [law] at result
  simpa only [actualFiniteClusterDegreeMeasure, Measure.map_id] using result

theorem actual_counting_projection_bound (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool)) (radius : ℝ) (nonnegative : 0 ≤ radius)
    (radiusBound : ∀ word : Fin (age + 1) → (Fin rule.edges × Bool),
      (markedTerminalComponentRadius rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened : ℝ) /
        scale ^ (fine + (age + 1) + 1) ≤ radius) :
    levyProkhorovEDist
      (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        scale scalePositive (fine + (age + 1)))
      ((fullComponentEmpiricalWordLaw rule marks crossing fine (age + 1) fallback).map
        (fun word => retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive age (fine + (age + 1)) (by omega)
          (actualComponentRetainedAnchor rule marks crossing age word))) ≤
        ENNReal.ofReal radius + actualFiniteClusterMeasure rule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + (age + 1))
          (actualComponentVertexFrontier rule marks crossing scale scalePositive fine (age + 1)) := by
  classical
  let anchor := fun word => retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive age (fine + (age + 1)) (by omega)
    (actualComponentRetainedAnchor rule marks crossing age word)
  have result := levyProkhorovEDist_map_le_of_exceptional_set
    (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (fine + (age + 1))) id
    (fun point => anchor (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point))
    (measurable_of_finite _) (measurable_of_finite _)
    (actualComponentVertexFrontier rule marks crossing scale scalePositive fine (age + 1)) radius nonnegative
    (Filter.Eventually.of_forall fun point outside =>
      (actualComponentVertexOwnership_distance_le rule marks crossing coherent scale scalePositive fine age fallback point outside).trans
        (radiusBound _))
  have law := congrArg (fun measure => measure.map anchor)
    (actualComponentVertexOwnership_law rule marks crossing scale scalePositive fine (age + 1) fallback)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at law
  simp only [Function.comp_def] at law
  rw [law] at result
  simpa only [Measure.map_id] using result

theorem actual_degree_counting_comparison_bound (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool)) (radius : ℝ) (nonnegative : 0 ≤ radius)
    (radiusBound : ∀ word : Fin (age + 1) → (Fin rule.edges × Bool),
      (markedTerminalComponentRadius rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened : ℝ) /
        scale ^ (fine + (age + 1) + 1) ≤ radius) :
    levyProkhorovEDist
      (actualFiniteClusterDegreeMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive (fine + (age + 1)))
      (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        scale scalePositive (fine + (age + 1))) ≤
      ENNReal.ofReal radius +
        (∑ word : Fin (age + 1) → (Fin rule.edges × Bool), ENNReal.ofReal
          |edgeComponentWordWeight rule marks fine (age + 1) word -
            fullComponentEmpiricalWordWeight rule marks fine (age + 1) fallback word|) +
        (ENNReal.ofReal radius + actualFiniteClusterMeasure rule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + (age + 1))
          (actualComponentVertexFrontier rule marks crossing scale scalePositive fine (age + 1))) := by
  let anchor := fun word => retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive age (fine + (age + 1)) (by omega)
    (actualComponentRetainedAnchor rule marks crossing age word)
  have degreeBound := actual_degree_projection_bound rule marks crossing coherent scale scalePositive fine age fallback radius nonnegative radiusBound
  have countingBound := actual_counting_projection_bound rule marks crossing coherent scale scalePositive fine age fallback radius nonnegative radiusBound
  have projectionBound := levyProkhorovEDist_finiteWeightPMF_map_le
    (edgeComponentWordWeight rule marks fine (age + 1)) (fullComponentEmpiricalWordWeight rule marks fine (age + 1) fallback)
    (edgeComponentWordWeight_nonnegative rule marks fine (age + 1))
    (fullComponentEmpiricalWordWeight_nonnegative rule marks fine (age + 1) fallback)
    (edgeComponentWordWeight_sum rule marks crossing fine (age + 1))
    (fullComponentEmpiricalWordWeight_sum rule marks crossing fine (age + 1) fallback) anchor (measurable_of_finite _)
  rw [levyProkhorovEDist_comm] at countingBound
  exact (levyProkhorovEDist_triangle _ _ _).trans
    (add_le_add ((levyProkhorovEDist_triangle _ _ _).trans (add_le_add degreeBound projectionBound)) countingBound)

end
end IGSIII34.Diffusion

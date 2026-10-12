import IGSIII34.Diffusion.ActualVertexResolventCompactnessCompletion
import IGSIII34.Diffusion.FiniteObjectivePassageCompletion
import IGSIII34.Diffusion.FiniteVertexMeasureCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology BigOperators

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

/-- The objective uses the actual reversible degree measure and all open
edges in the original retained source component. -/
def actualOriginalCountingObjectiveCompletion (depth : ℕ) (parameter : ℝ)
    (forcing : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → ℝ)
    (potential : Fin (rule.generation depth).vertices → ℝ) : ℝ :=
  parameter * (∫ vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth,
      potential vertex.val ^ 2 ∂actualFiniteClusterMeasure rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth) +
    sourceComponentEnergy (network (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (fun _ => (growth ^ (depth + 1))⁻¹) potential -
    2 * (∫ vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth,
      forcing vertex * potential vertex.val ∂actualFiniteClusterMeasure rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth)

/-- The finite potential is the genuine paper-clock resolvent. Its minimum
is compared with every original full-generation test potential. -/
theorem actualOriginalVertexClockResolvent_minimizes_completion
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (forcing : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth → ℝ)
    (depth : ℕ) (test : Fin (rule.generation depth).vertices → ℝ) :
    actualOriginalCountingObjectiveCompletion rule p positive belowOne fixedPoint growth value marks
      chemicalScale chemicalScalePositive depth parameter (forcing depth)
      (actualOriginalVertexClockResolventPotentialCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive parameter parameterPositive forcing depth) ≤
    actualOriginalCountingObjectiveCompletion rule p positive belowOne fixedPoint growth value marks
      chemicalScale chemicalScalePositive depth parameter (forcing depth) test := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  have minimum := finiteVertexResolvent_minimizes_completion
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    parameter (growth ^ (depth + 1)) parameterPositive (pow_pos growthPositive _).le (forcing depth) (fun vertex => test vertex.val)
  rw [finiteVertexResolventFunctional_integral_completion, finiteVertexResolventFunctional_integral_completion] at minimum
  unfold actualOriginalCountingObjectiveCompletion
  rw [sourceEnergy_constant_inverse_scale_completion, sourceEnergy_constant_inverse_scale_completion,
    sourceComponentEnergy_eq_cluster_energy_completion, sourceComponentEnergy_eq_cluster_energy_completion]
  have restricted : (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
      actualOriginalVertexClockResolventPotentialCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive parameter parameterPositive forcing depth vertex.val) =
      actualVertexClockGraphResolventCompletion rule (stationaryConfiguration rule marks.val)
        (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
        chemicalScale chemicalScalePositive depth growth growthPositive parameter parameterPositive (forcing depth) := by
    funext vertex
    exact retainedPotentialExtension_retained_completion _ _ _ vertex
  have restrictedVertex (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) := congrFun restricted vertex
  simp only [restrictedVertex]
  exact minimum

end
end IGSIII34.Diffusion





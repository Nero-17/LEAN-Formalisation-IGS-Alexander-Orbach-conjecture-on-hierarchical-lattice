import IGSIII34.Spectral.Collars.ActualFiniteAnnealedStartingPoints
import IGSIII34.Diffusion.DiscreteCadlagWeakCompletion
import IGSIII34.Diffusion.FiniteWeightedCadlagLawCompletion
import Mathlib.MeasureTheory.Measure.DiracProba

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped _root_.Topology

theorem discreteCadlagProbability_placement_map
    {Vertex First Second : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [MetricSpace First] [CompactSpace First] [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Second] [CompactSpace Second] [MeasurableSpace Second] [BorelSpace Second]
    (law : ProbabilityMeasure (ℕ → Vertex)) (clock : ℝ) (positive : 0 < clock)
    (placement : Vertex → First) (map : First → Second) (continuous : Continuous map) :
    (discreteCadlagProbabilityCompletion law clock positive placement).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion map continuous).measurable.aemeasurable =
    discreteCadlagProbabilityCompletion law clock positive (map ∘ placement) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure (ℕ → Vertex)).map (discreteCadlagSampleCompletion clock positive placement)).map
    (skorokhodCadlagContinuousCarrierMapCompletion map continuous) =
    (law : Measure (ℕ → Vertex)).map (discreteCadlagSampleCompletion clock positive (map ∘ placement))
  rw [AEMeasurable.map_map_of_aemeasurable
    (skorokhodCadlagContinuousCarrierMap_continuous_completion map continuous).measurable.aemeasurable
    (discreteCadlagSample_measurable_completion clock positive placement).aemeasurable]
  rfl

theorem holdingCadlagProbability_placement_map
    {Vertex First Second : Type*} [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]
    [MetricSpace First] [CompactSpace First] [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Second] [CompactSpace Second] [MeasurableSpace Second] [BorelSpace Second]
    (law : ProbabilityMeasure ((ℕ → Vertex) × (ℕ → ℝ)))
    (regular : ∀ᵐ sample ∂(law : Measure ((ℕ → Vertex) × (ℕ → ℝ))), (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (clock : ℝ) (positive : 0 < clock) (placement : Vertex → First)
    (map : First → Second) (continuous : Continuous map) :
    (holdingCadlagProbabilityCompletion law regular clock positive placement).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion map continuous).measurable.aemeasurable =
    holdingCadlagProbabilityCompletion law regular clock positive (map ∘ placement) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((law : Measure ((ℕ → Vertex) × (ℕ → ℝ))).map (holdingCadlagSampleCompletion clock positive placement)).map
    (skorokhodCadlagContinuousCarrierMapCompletion map continuous) =
    (law : Measure ((ℕ → Vertex) × (ℕ → ℝ))).map (holdingCadlagSampleCompletion clock positive (map ∘ placement))
  rw [AEMeasurable.map_map_of_aemeasurable
    (skorokhodCadlagContinuousCarrierMap_continuous_completion map continuous).measurable.aemeasurable
    (holdingCadlagSample_aemeasurable_completion (law : Measure _) regular clock positive placement)]
  apply Measure.map_congr
  apply Filter.Eventually.of_forall
  intro sample
  apply Subtype.ext
  classical
  by_cases condition : (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop
  · simp only [Function.comp_apply, holdingCadlagSampleCompletion, dif_pos condition]
    rfl
  · simp only [Function.comp_apply, holdingCadlagSampleCompletion, dif_neg condition]
    rfl

theorem finiteWeightedCadlagProbability_placement_map
    {Vertex Edge First Second : Type*} [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    [MetricSpace First] [CompactSpace First] [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Second] [CompactSpace Second] [MeasurableSpace Second] [BorelSpace Second]
    (endpoint : Edge → Vertex × Vertex) (degreePositive : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (weight : Vertex → ℝ) (weightPositive : ∀ vertex, 0 < weight vertex)
    (clock : ℝ) (positive : 0 < clock) (placement : Vertex → First)
    (map : First → Second) (continuous : Continuous map) :
    (finiteWeightedCadlagProbabilityCompletion endpoint degreePositive initial weight weightPositive clock positive placement).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion map continuous).measurable.aemeasurable =
    finiteWeightedCadlagProbabilityCompletion endpoint degreePositive initial weight weightPositive clock positive (map ∘ placement) := by
  unfold finiteWeightedCadlagProbabilityCompletion weightedHoldingCadlagProbabilityCompletion
  exact holdingCadlagProbability_placement_map _ _ _ _ _ _ _

variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

/-- The original whole path law on the genuine finite chemical metric carrier.
The three clock choices are discrete, rate one and inverse degree. -/
def actualFiniteAnnealedCanonicalPathLaw
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion
      (ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)) := by
  classical
  let endpoint := clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
  have degreePositive := cluster_degree_positive (rule.generation depth).network
    (configurationAtDepth rule depth configuration depth) (by simpa only [configurationAtDepth_self] using crossing)
  let vertex := actualFiniteAnnealedInitialVertex rule scale scalePositive depth configuration initial
  if discrete : kind = 0 then
    exact discreteCadlagProbabilityCompletion
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)
      (⟨finiteDiscreteWalkLaw (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) endpoint degreePositive (Measure.dirac vertex), inferInstance⟩ : ProbabilityMeasure _)
      clock clockPositive id
  else
    exact finiteWeightedCadlagProbabilityCompletion
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)
      endpoint degreePositive (diracProba vertex)
      (fun point => if kind = 1 then 1 else (degree endpoint point)⁻¹)
      (fun point => by split_ifs <;> first | exact zero_lt_one | exact inv_pos.mpr (degreePositive point))
      clock clockPositive id

def actualFiniteAnnealedPlacedPathLaw
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3)
    (placement : ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth → Space) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion Space) := by
  classical
  let endpoint := clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
  have degreePositive := cluster_degree_positive (rule.generation depth).network
    (configurationAtDepth rule depth configuration depth) (by simpa only [configurationAtDepth_self] using crossing)
  let vertex := actualFiniteAnnealedInitialVertex rule scale scalePositive depth configuration initial
  if discrete : kind = 0 then
    exact discreteCadlagProbabilityCompletion
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)
      (⟨finiteDiscreteWalkLaw (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) endpoint degreePositive (Measure.dirac vertex), inferInstance⟩ : ProbabilityMeasure _)
      clock clockPositive placement
  else
    exact finiteWeightedCadlagProbabilityCompletion
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)
      endpoint degreePositive (diracProba vertex)
      (fun point => if kind = 1 then 1 else (degree endpoint point)⁻¹)
      (fun point => by split_ifs <;> first | exact zero_lt_one | exact inv_pos.mpr (degreePositive point))
      clock clockPositive placement

/-- Every physical placement, in particular each isometric placement in
the same master ambient, is exactly a carrier map of the original law. -/
theorem actualFiniteAnnealedPlacedPathLaw_eq_canonical_map
    {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3)
    (placement : ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth → Space)
    (continuous : Continuous placement) :
    actualFiniteAnnealedPlacedPathLaw rule scale scalePositive depth configuration crossing initial clock clockPositive kind placement =
    (actualFiniteAnnealedCanonicalPathLaw rule scale scalePositive depth configuration crossing initial clock clockPositive kind).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion placement continuous).measurable.aemeasurable := by
  classical
  unfold actualFiniteAnnealedPlacedPathLaw actualFiniteAnnealedCanonicalPathLaw
  dsimp only
  split_ifs with discrete
  · exact (discreteCadlagProbability_placement_map _ _ _ id placement continuous).symm
  all_goals exact (finiteWeightedCadlagProbability_placement_map _ _ _ _ _ _ _ id placement continuous).symm

end
end IGSIII34.Spectral

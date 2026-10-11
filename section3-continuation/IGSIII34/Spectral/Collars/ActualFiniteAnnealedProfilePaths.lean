import IGSIII34.Spectral.Collars.ActualFiniteAnnealedWholePath
import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCanonicalPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion MeasureTheory ProbabilityTheory
open scoped _root_.Topology NNReal
variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

def actualFiniteAnnealedProfilePathResponse
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule))) := by
  classical
  if crossing : (rule.generation depth).network.crosses input.1 = true then
    if positive : 0 < clock input.1 then
      exact actualFiniteAnnealedWholePathLaw rule scale scalePositive depth input.1 crossing input.2 (clock input.1) positive kind
    else
      exact diracProba ⟨⟨fun _ _ => ⟨0, le_rfl, zero_le_one⟩⟩, continuous_path_cadlag_completion20261011 _ continuous_const⟩
  else
    exact diracProba ⟨⟨fun _ _ => ⟨0, le_rfl, zero_le_one⟩⟩, continuous_path_cadlag_completion20261011 _ continuous_const⟩

def actualFiniteAnnealedProfileObservationResponse
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    ProbabilityMeasure (ℕ → CountableDistanceProfile (ActualAnnealedBirthLabels rule)) := by
  classical
  if crossing : (rule.generation depth).network.crosses input.1 = true then
    let sampleLaw := finiteContinuousWalkSampleLaw
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth input.1) scale scalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth input.1 depth))
      (cluster_degree_positive (rule.generation depth).network _ (by simpa only [configurationAtDepth_self] using crossing))
      (Measure.dirac (actualFiniteAnnealedInitialVertex rule scale scalePositive depth input.1 input.2))
    let sample := fun outcome time => actualFiniteAnnealedCompactProfile rule scale scalePositive depth input.1
      (actualFiniteAnnealedObservedPath rule scale scalePositive depth input.1 times (clock input.1) kind outcome time)
    have measurable : Measurable sample := by
      apply measurable_pi_lambda
      intro time
      exact (measurable_of_finite (actualFiniteAnnealedCompactProfile rule scale scalePositive depth input.1)).comp
        ((measurable_pi_apply time).comp
          (actualFiniteAnnealedObservedPath_measurable rule scale scalePositive depth input.1 times (clock input.1) kind))
    exact ⟨sampleLaw.map sample, Measure.isProbabilityMeasure_map measurable.aemeasurable⟩
  else
    exact diracProba (fun _ _ => ⟨0, le_rfl, zero_le_one⟩)

def actualFiniteAnnealedProfilePathKernel
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    Kernel (((List (Fin rule.edges) × Bool) → Configuration rule.edges))
      (SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule))) :=
  (Kernel.ofFunOfCountable (fun input => (actualFiniteAnnealedProfilePathResponse rule scale scalePositive depth clock kind input :
    Measure (SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule)))))).comap
    (fun marks => (markedGenerationConfiguration rule marks depth [] true, initial marks))
    ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

instance actualFiniteAnnealedProfilePathKernel_markov
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    IsMarkovKernel (actualFiniteAnnealedProfilePathKernel rule scale scalePositive depth clock kind initial initialMeasurable) := by
  constructor
  intro marks
  change IsProbabilityMeasure (actualFiniteAnnealedProfilePathResponse rule scale scalePositive depth clock kind
    (markedGenerationConfiguration rule marks depth [] true, initial marks) :
    Measure (SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule))))
  infer_instance

theorem actualFiniteAnnealedProfileObservationResponse_borel_measurable
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ℕ → CountableDistanceProfile (ActualAnnealedBirthLabels rule))))
      (fun marks => actualFiniteAnnealedProfileObservationResponse rule scale scalePositive depth times clock kind
        (markedGenerationConfiguration rule marks depth [] true, initial marks)) := by
  have response : @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ℕ → CountableDistanceProfile (ActualAnnealedBirthLabels rule))))
      (actualFiniteAnnealedProfileObservationResponse rule scale scalePositive depth times clock kind) :=
    @measurable_of_finite _ _ inferInstance (borel (ProbabilityMeasure (ℕ → CountableDistanceProfile (ActualAnnealedBirthLabels rule)))) inferInstance inferInstance _
  exact @Measurable.comp _ _ _ inferInstance inferInstance (borel (ProbabilityMeasure (ℕ → CountableDistanceProfile (ActualAnnealedBirthLabels rule)))) _ _
    response ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

end
end IGSIII34.Spectral

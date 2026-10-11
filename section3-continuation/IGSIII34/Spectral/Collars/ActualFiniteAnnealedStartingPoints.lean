import IGSIII34.Spectral.Collars.ActualFiniteAnnealedCoding
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal
variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

/-- A global vertex selector is retained whenever it belongs to the true
cluster; its value on excluded vertices is the persistent source. -/
def actualFiniteAnnealedInitialVertex
    (configuration : Configuration (rule.generation depth).edges)
    (vertex : Fin (rule.generation depth).vertices) :
    ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth := by
  classical
  by_cases retained : ((rule.generation depth).network.openGraph configuration).Reachable
      (rule.generation depth).network.source vertex
  · exact ⟨vertex, by simpa only [configurationAtDepth_self] using retained⟩
  · exact ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩

def actualFiniteAnnealedStartedResponse
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    Measure (ActualAnnealedFiniteCode rule) := by
  classical
  by_cases crossing : (rule.generation depth).network.crosses input.1 = true
  · exact (finiteContinuousWalkSampleLaw
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth input.1) scale scalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth input.1 depth))
      (cluster_degree_positive (rule.generation depth).network _ (by simpa only [configurationAtDepth_self] using crossing))
      (Measure.dirac (actualFiniteAnnealedInitialVertex rule scale scalePositive depth input.1 input.2))).map
      (actualFiniteAnnealedPathCode rule scale scalePositive depth input.1 crossing ∘
        actualFiniteAnnealedObservedPath rule scale scalePositive depth input.1 times (clock input.1) kind)
  · exact Measure.dirac (fun _ => 0, fun _ _ => 0, fun _ _ => 0)

instance actualFiniteAnnealedStartedResponse_probability
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    IsProbabilityMeasure (actualFiniteAnnealedStartedResponse rule scale scalePositive depth times clock kind input) := by
  classical
  unfold actualFiniteAnnealedStartedResponse
  split_ifs with crossing
  · exact isProbabilityMeasure_map ((actualFiniteAnnealedPathCode_measurable rule scale scalePositive depth input.1 crossing).comp
      (actualFiniteAnnealedObservedPath_measurable rule scale scalePositive depth input.1 times (clock input.1) kind)).aemeasurable
  · infer_instance

def actualFiniteAnnealedStartedConfigurationKernel
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    Kernel (Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) (ActualAnnealedFiniteCode rule) :=
  Kernel.ofFunOfCountable (actualFiniteAnnealedStartedResponse rule scale scalePositive depth times clock kind)

instance actualFiniteAnnealedStartedConfigurationKernel_markov
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    IsMarkovKernel (actualFiniteAnnealedStartedConfigurationKernel rule scale scalePositive depth times clock kind) := by
  constructor
  intro input
  change IsProbabilityMeasure (actualFiniteAnnealedStartedResponse rule scale scalePositive depth times clock kind input)
  infer_instance

/-- The only selector requirement is the legitimate measurability of the
random starting vertices. Measurability of the actual path law is proved. -/
def actualFiniteAnnealedStartedEnvironmentKernel
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    Kernel (((List (Fin rule.edges) × Bool) → Configuration rule.edges)) (ActualAnnealedFiniteCode rule) :=
  (actualFiniteAnnealedStartedConfigurationKernel rule scale scalePositive depth times clock kind).comap
    (fun marks => (markedGenerationConfiguration rule marks depth [] true, initial marks))
    ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

instance actualFiniteAnnealedStartedEnvironmentKernel_markov
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    IsMarkovKernel (actualFiniteAnnealedStartedEnvironmentKernel rule scale scalePositive depth times clock kind initial initialMeasurable) := by
  unfold actualFiniteAnnealedStartedEnvironmentKernel
  infer_instance

theorem actualFiniteAnnealedStartedEnvironmentProbability_borel_measurable
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule)))
      (fun marks => (⟨actualFiniteAnnealedStartedEnvironmentKernel rule scale scalePositive depth times clock kind initial initialMeasurable marks,
        inferInstance⟩ : ProbabilityMeasure (ActualAnnealedFiniteCode rule))) := by
  have finiteResponse : @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule)))
      (fun input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices =>
        (⟨actualFiniteAnnealedStartedResponse rule scale scalePositive depth times clock kind input,
          inferInstance⟩ : ProbabilityMeasure (ActualAnnealedFiniteCode rule))) :=
    @measurable_of_finite _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule))) inferInstance inferInstance _
  exact @Measurable.comp _ _ _ inferInstance inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule))) _ _
    finiteResponse ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

end
end IGSIII34.Spectral

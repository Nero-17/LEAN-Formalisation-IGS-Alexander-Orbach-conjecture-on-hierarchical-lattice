import IGSIII.Geometry.CellLocalisationGH
import IGSIII34.Diffusion.ContinuousWalkConstruction
import IGSIII34.Diffusion.FiniteWeightedHoldingPathsCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped BigOperators NNReal

/-- Deterministic labels include every vertex at every birth generation. -/
def ActualAnnealedBirthLabels (rule : Rule) := Σ age, Fin (rule.generation age).vertices

instance actualAnnealedBirthLabelsCountable (rule : Rule) : Countable (ActualAnnealedBirthLabels rule) :=
  inferInstanceAs (Countable (Σ age, Fin (rule.generation age).vertices))

/-- One fixed measurable target retains geometry, both mass moment families,
and every prescribed time observation of the actual walk. -/
def ActualAnnealedFiniteCode (rule : Rule) :=
  ((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
  (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) ×
  (ℕ → ActualAnnealedBirthLabels rule → ℝ)

instance actualAnnealedFiniteCodeMeasurable (rule : Rule) : MeasurableSpace (ActualAnnealedFiniteCode rule) :=
  inferInstanceAs (MeasurableSpace (((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
    (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) × (ℕ → ActualAnnealedBirthLabels rule → ℝ)))

variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

def actualFiniteAnnealedBirthProjection
    (configuration : Configuration (rule.generation depth).edges)
    (label : ActualAnnealedBirthLabels rule) :
    ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth := by
  classical
  by_cases bound : label.1 ≤ depth
  · let vertex := persistentVertexEmbedding rule label.1 depth bound label.2
    by_cases retained : ((rule.generation depth).network.openGraph configuration).Reachable
        (rule.generation depth).network.source vertex
    · exact ⟨vertex, by simpa only [configurationAtDepth_self] using retained⟩
    · exact ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩
  · exact ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩

def actualFiniteAnnealedDistanceProfile
    (configuration : Configuration (rule.generation depth).edges)
    (vertex : ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)
    (label : ActualAnnealedBirthLabels rule) : ℝ :=
  dist vertex (actualFiniteAnnealedBirthProjection rule scale scalePositive depth configuration label)

def actualFiniteAnnealedMassMoments
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (counting : Bool) (labels : List (ActualAnnealedBirthLabels rule)) : ℝ := by
  letI := clusterEdge_nonempty (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
    (by simpa only [configurationAtDepth_self] using crossing)
  let measure : Measure (ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) :=
    if counting then uniformOn Set.univ else
      degreeMeasure (clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth configuration depth))
  exact ∫ vertex, (labels.map (fun label => Real.exp (-actualFiniteAnnealedDistanceProfile
    rule scale scalePositive depth configuration vertex label))).prod ∂measure

def actualFiniteAnnealedPathCode
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (path : ℕ → ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) :
    ActualAnnealedFiniteCode rule :=
  (fun pair => dist (actualFiniteAnnealedBirthProjection rule scale scalePositive depth configuration pair.1)
    (actualFiniteAnnealedBirthProjection rule scale scalePositive depth configuration pair.2),
    actualFiniteAnnealedMassMoments rule scale scalePositive depth configuration crossing,
    fun time label => actualFiniteAnnealedDistanceProfile rule scale scalePositive depth configuration (path time) label)

theorem actualFiniteAnnealedPathCode_measurable
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true) :
    Measurable (actualFiniteAnnealedPathCode rule scale scalePositive depth configuration crossing) := by
  apply measurable_const.prodMk
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro time
  apply measurable_pi_lambda
  intro label
  exact (measurable_of_finite (fun vertex => actualFiniteAnnealedDistanceProfile
    rule scale scalePositive depth configuration vertex label)).comp (measurable_pi_apply time)

/-- The three original clocks are encoded on the same neighbour-chain and
iid exponential sample. Clock 0 is discrete, 1 is rate one, 2 is inverse degree. -/
def actualFiniteAnnealedObservedPath
    (configuration : Configuration (rule.generation depth).edges)
    (times : ℕ → ℝ≥0) (clock : ℝ≥0) (kind : Fin 3)
    (sample : (ℕ → ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) × (ℕ → ℝ))
    (time : ℕ) : ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth :=
  if kind = 0 then sample.1 ⌊(clock * times time : ℝ≥0)⌋₊ else
    finiteContinuousWalkPath
      (weightedHoldingSampleCompletion20261011
        (fun vertex => if kind = 1 then 1 else
          (degree (clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth configuration depth)) vertex)⁻¹) sample)
      (clock * times time)

theorem actualFiniteAnnealedObservedPath_measurable
    (configuration : Configuration (rule.generation depth).edges)
    (times : ℕ → ℝ≥0) (clock : ℝ≥0) (kind : Fin 3) :
    Measurable (actualFiniteAnnealedObservedPath rule scale scalePositive depth configuration times clock kind) := by
  classical
  apply measurable_pi_lambda
  intro time
  by_cases discrete : kind = 0
  · simp only [actualFiniteAnnealedObservedPath, discrete, if_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [actualFiniteAnnealedObservedPath, discrete, if_false]
    exact (holdingTimePath_measurable _).comp
      (weightedHoldingSample_measurable_completion20261011 _)

def actualFiniteAnnealedConditionalResponse
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (configuration : Configuration (rule.generation depth).edges) : Measure (ActualAnnealedFiniteCode rule) := by
  classical
  by_cases crossing : (rule.generation depth).network.crosses configuration = true
  · let endpoint := clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
    let initial : ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth :=
      ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩
    exact (finiteContinuousWalkSampleLaw (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) endpoint
      (cluster_degree_positive (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
        (by simpa only [configurationAtDepth_self] using crossing)) (Measure.dirac initial)).map
      (actualFiniteAnnealedPathCode rule scale scalePositive depth configuration crossing ∘
        actualFiniteAnnealedObservedPath rule scale scalePositive depth configuration times (clock configuration) kind)
  · exact Measure.dirac (fun _ => 0, fun _ _ => 0, fun _ _ => 0)

instance actualFiniteAnnealedConditionalResponse_probability
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (configuration : Configuration (rule.generation depth).edges) :
    IsProbabilityMeasure (actualFiniteAnnealedConditionalResponse rule scale scalePositive depth times clock kind configuration) := by
  classical
  unfold actualFiniteAnnealedConditionalResponse
  split_ifs with crossing
  · exact isProbabilityMeasure_map ((actualFiniteAnnealedPathCode_measurable rule scale scalePositive depth configuration crossing).comp
      (actualFiniteAnnealedObservedPath_measurable rule scale scalePositive depth configuration times (clock configuration) kind)).aemeasurable
  · infer_instance

def actualFiniteAnnealedConfigurationKernel
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    Kernel (Configuration (rule.generation depth).edges) (ActualAnnealedFiniteCode rule) :=
  Kernel.ofFunOfCountable (actualFiniteAnnealedConditionalResponse rule scale scalePositive depth times clock kind)

instance actualFiniteAnnealedConfigurationKernel_markov
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    IsMarkovKernel (actualFiniteAnnealedConfigurationKernel rule scale scalePositive depth times clock kind) := by
  constructor
  intro configuration
  change IsProbabilityMeasure (actualFiniteAnnealedConditionalResponse rule scale scalePositive depth times clock kind configuration)
  infer_instance

/-- Actual environment measurability is discharged by the genuine finite
configuration map, without any measurable-selection premise. -/
def actualFiniteAnnealedEnvironmentKernel
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    Kernel (((List (Fin rule.edges) × Bool) → Configuration rule.edges)) (ActualAnnealedFiniteCode rule) :=
  (actualFiniteAnnealedConfigurationKernel rule scale scalePositive depth times clock kind).comap
    (fun marks => markedGenerationConfiguration rule marks depth [] true)
    (markedGenerationConfiguration_measurable rule depth [] true)

instance actualFiniteAnnealedEnvironmentKernel_markov
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    IsMarkovKernel (actualFiniteAnnealedEnvironmentKernel rule scale scalePositive depth times clock kind) := by
  unfold actualFiniteAnnealedEnvironmentKernel
  infer_instance

instance actualAnnealedFiniteCodeTopological (rule : Rule) : TopologicalSpace (ActualAnnealedFiniteCode rule) :=
  inferInstanceAs (TopologicalSpace (((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
    (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) × (ℕ → ActualAnnealedBirthLabels rule → ℝ)))

instance actualAnnealedFiniteCodeBorel (rule : Rule) : BorelSpace (ActualAnnealedFiniteCode rule) :=
  inferInstanceAs (BorelSpace (((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
    (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) × (ℕ → ActualAnnealedBirthLabels rule → ℝ)))

instance actualAnnealedFiniteCodePolish (rule : Rule) : PolishSpace (ActualAnnealedFiniteCode rule) :=
  inferInstanceAs (PolishSpace (((ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule) → ℝ) ×
    (Bool → List (ActualAnnealedBirthLabels rule) → ℝ) × (ℕ → ActualAnnealedBirthLabels rule → ℝ)))

def actualFiniteAnnealedEnvironmentProbability
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ProbabilityMeasure (ActualAnnealedFiniteCode rule) :=
  ⟨actualFiniteAnnealedEnvironmentKernel rule scale scalePositive depth times clock kind marks, inferInstance⟩

theorem actualFiniteAnnealedEnvironmentProbability_measurable
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    Measurable (actualFiniteAnnealedEnvironmentProbability rule scale scalePositive depth times clock kind) := by
  have finiteResponse : Measurable (fun configuration : Configuration (rule.generation depth).edges =>
      (⟨actualFiniteAnnealedConditionalResponse rule scale scalePositive depth times clock kind configuration,
        inferInstance⟩ : ProbabilityMeasure (ActualAnnealedFiniteCode rule))) := measurable_of_finite _
  exact finiteResponse.comp (markedGenerationConfiguration_measurable rule depth [] true)

theorem actualFiniteAnnealedEnvironmentProbability_borel_measurable
    (times : ℕ → ℝ≥0) (clock : Configuration (rule.generation depth).edges → ℝ≥0) (kind : Fin 3) :
    @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule)))
      (actualFiniteAnnealedEnvironmentProbability rule scale scalePositive depth times clock kind) := by
  have finiteResponse : @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule))) (fun configuration : Configuration (rule.generation depth).edges =>
      (⟨actualFiniteAnnealedConditionalResponse rule scale scalePositive depth times clock kind configuration,
        inferInstance⟩ : ProbabilityMeasure (ActualAnnealedFiniteCode rule))) :=
    @measurable_of_finite _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule))) inferInstance inferInstance _
  exact @Measurable.comp _ _ _ inferInstance inferInstance (borel (ProbabilityMeasure (ActualAnnealedFiniteCode rule))) _ _
    finiteResponse (markedGenerationConfiguration_measurable rule depth [] true)

/-- Actual population clocks: twice retained edge count for the simple/rate-one
walk, and retained vertex count for the inverse-degree holding-time walk. -/
def actualFiniteAnnealedNaturalClock (resistanceScale : ℝ) (kind : Fin 3)
    (configuration : Configuration (rule.generation depth).edges) : ℝ≥0 :=
  Real.toNNReal ((if kind = 2 then
    (Nat.card (ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) : ℝ)
    else 2 * (rule.generation depth).network.liveCount .connected .connected configuration) * resistanceScale ^ (depth + 1))

theorem actualFiniteAnnealedNaturalKernel_crossing
    (resistanceScale : ℝ) (times : ℕ → ℝ≥0) (kind : Fin 3)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : (rule.generation depth).network.crosses (markedGenerationConfiguration rule marks depth [] true) = true) :
    actualFiniteAnnealedEnvironmentKernel rule scale scalePositive depth times
      (actualFiniteAnnealedNaturalClock rule scale scalePositive depth resistanceScale kind) kind marks =
    (finiteContinuousWalkSampleLaw
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth (markedGenerationConfiguration rule marks depth [] true)) scale scalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network
        (configurationAtDepth rule depth (markedGenerationConfiguration rule marks depth [] true) depth))
      (cluster_degree_positive (rule.generation depth).network _ (by simpa only [configurationAtDepth_self] using crossing))
      (Measure.dirac ⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩)).map
      (actualFiniteAnnealedPathCode rule scale scalePositive depth _ crossing ∘
        actualFiniteAnnealedObservedPath rule scale scalePositive depth _ times
          (actualFiniteAnnealedNaturalClock rule scale scalePositive depth resistanceScale kind
            (markedGenerationConfiguration rule marks depth [] true)) kind) := by
  classical
  change actualFiniteAnnealedConditionalResponse rule scale scalePositive depth times
    (actualFiniteAnnealedNaturalClock rule scale scalePositive depth resistanceScale kind) kind
      (markedGenerationConfiguration rule marks depth [] true) = _
  simp only [actualFiniteAnnealedConditionalResponse, crossing, dif_pos]

end
end IGSIII34.Spectral

import IGSIII34.Spectral.Collars.ActualFiniteAnnealedStartingPoints
import IGSIII34.Diffusion.CountableDistanceProfile
import IGSIII34.Diffusion.DiscreteCadlagWeakCompletion20261011
import IGSIII34.Diffusion.FiniteWeightedCadlagLawCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion MeasureTheory MeasureTheory.Measure ProbabilityTheory GromovHausdorff
open scoped _root_.Topology

variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

def actualFiniteAnnealedCompactProfile
    (configuration : Configuration (rule.generation depth).edges) :
    ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth →
      CountableDistanceProfile (ActualAnnealedBirthLabels rule) :=
  distanceProfilePoint (actualFiniteAnnealedBirthProjection rule scale scalePositive depth configuration)

def actualFiniteAnnealedCompactMass
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true) (counting : Bool) :
    ProbabilityMeasure (CountableDistanceProfile (ActualAnnealedBirthLabels rule)) := by
  letI := clusterEdge_nonempty (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
    (by simpa only [configurationAtDepth_self] using crossing)
  let mass : ProbabilityMeasure (ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth) :=
    if counting then ⟨uniformOn Set.univ, inferInstance⟩ else
      ⟨degreeMeasure (clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth configuration depth)), inferInstance⟩
  exact ProbabilityMeasure.map mass (measurable_of_finite
    (actualFiniteAnnealedCompactProfile rule scale scalePositive depth configuration)).aemeasurable

/-- Genuine full paths, with their original discrete or exponential clocks,
are placed in the one fixed compact countable distance-profile space. -/
def actualFiniteAnnealedWholePathLaw
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (initial : Fin (rule.generation depth).vertices)
    (clock : ℝ) (clockPositive : 0 < clock) (kind : Fin 3) :
    ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule))) := by
  classical
  let endpoint := clusterRetainedEndpoint (rule.generation depth).network (configurationAtDepth rule depth configuration depth)
  have degreePositive := cluster_degree_positive (rule.generation depth).network
    (configurationAtDepth rule depth configuration depth) (by simpa only [configurationAtDepth_self] using crossing)
  let vertex := actualFiniteAnnealedInitialVertex rule scale scalePositive depth configuration initial
  if discrete : kind = 0 then
    exact discreteCadlagProbabilityCompletion20261011
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)
      (⟨finiteDiscreteWalkLaw endpoint degreePositive (Measure.dirac vertex), inferInstance⟩ : ProbabilityMeasure _)
      clock clockPositive (actualFiniteAnnealedCompactProfile rule scale scalePositive depth configuration)
  else
    exact finiteWeightedCadlagProbabilityCompletion20261011
      (Vertex := ActualFiniteCluster rule (configurationAtDepth rule depth configuration) scale scalePositive depth)
      endpoint degreePositive (diracProba vertex)
      (fun point => if kind = 1 then 1 else (degree endpoint point)⁻¹)
      (fun point => by split_ifs <;> first | exact zero_lt_one | exact inv_pos.mpr (degreePositive point))
      clock clockPositive (actualFiniteAnnealedCompactProfile rule scale scalePositive depth configuration)

/-- Geometry and both actual masses are retained jointly with the whole
càdlàg path. No rational-time-only topology is substituted here. -/
def ActualAnnealedWholeCode (rule : Rule) :=
  GHSpace × (Bool → ProbabilityMeasure (CountableDistanceProfile (ActualAnnealedBirthLabels rule))) ×
    SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule))

instance actualAnnealedWholeCodeTopology (rule : Rule) : TopologicalSpace (ActualAnnealedWholeCode rule) :=
  inferInstanceAs (TopologicalSpace (GHSpace ×
    (Bool → ProbabilityMeasure (CountableDistanceProfile (ActualAnnealedBirthLabels rule))) ×
    SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule))))
instance actualAnnealedWholeCodeMeasurable (rule : Rule) : MeasurableSpace (ActualAnnealedWholeCode rule) := borel _
instance actualAnnealedWholeCodeBorel (rule : Rule) : BorelSpace (ActualAnnealedWholeCode rule) := ⟨rfl⟩

def actualFiniteAnnealedWholeResponse
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    ProbabilityMeasure (ActualAnnealedWholeCode rule) := by
  classical
  let geometry := toGHSpace (ActualFiniteCluster rule (configurationAtDepth rule depth input.1) scale scalePositive depth)
  if crossing : (rule.generation depth).network.crosses input.1 = true then
    if positive : 0 < clock input.1 then
      let attach : SkorokhodCadlagPathCompletion20261011 (CountableDistanceProfile (ActualAnnealedBirthLabels rule)) → ActualAnnealedWholeCode rule :=
        fun path => (geometry, actualFiniteAnnealedCompactMass rule scale scalePositive depth input.1 crossing, path)
      have continuous : Continuous attach := continuous_const.prodMk (continuous_const.prodMk continuous_id)
      exact ProbabilityMeasure.map (actualFiniteAnnealedWholePathLaw rule scale scalePositive depth input.1 crossing
        input.2 (clock input.1) positive kind) continuous.measurable.aemeasurable
    else
      exact diracProba (geometry, fun _ => diracProba (fun _ => ⟨0, le_rfl, zero_le_one⟩),
        ⟨⟨fun _ _ => ⟨0, le_rfl, zero_le_one⟩⟩, continuous_path_cadlag_completion20261011 _ continuous_const⟩)
  else
    exact diracProba (geometry, fun _ => diracProba (fun _ => ⟨0, le_rfl, zero_le_one⟩),
      ⟨⟨fun _ _ => ⟨0, le_rfl, zero_le_one⟩⟩, continuous_path_cadlag_completion20261011 _ continuous_const⟩)

def actualFiniteAnnealedWholeConfigurationKernel
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3) :
    Kernel (Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) (ActualAnnealedWholeCode rule) :=
  Kernel.ofFunOfCountable (fun input => (actualFiniteAnnealedWholeResponse rule scale scalePositive depth clock kind input : Measure _))

instance actualFiniteAnnealedWholeConfigurationKernel_markov
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3) :
    IsMarkovKernel (actualFiniteAnnealedWholeConfigurationKernel rule scale scalePositive depth clock kind) := by
  constructor
  intro input
  change IsProbabilityMeasure (actualFiniteAnnealedWholeResponse rule scale scalePositive depth clock kind input : Measure _)
  infer_instance

/-- Arbitrary measurable random starting vertices are allowed. The finite
conditional geometry/mass/whole-path law has proved environment measurability. -/
def actualFiniteAnnealedWholeEnvironmentKernel
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    Kernel (((List (Fin rule.edges) × Bool) → Configuration rule.edges)) (ActualAnnealedWholeCode rule) :=
  (actualFiniteAnnealedWholeConfigurationKernel rule scale scalePositive depth clock kind).comap
    (fun marks => (markedGenerationConfiguration rule marks depth [] true, initial marks))
    ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

instance actualFiniteAnnealedWholeEnvironmentKernel_markov
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    IsMarkovKernel (actualFiniteAnnealedWholeEnvironmentKernel rule scale scalePositive depth clock kind initial initialMeasurable) := by
  unfold actualFiniteAnnealedWholeEnvironmentKernel
  infer_instance

theorem actualFiniteAnnealedWholeResponse_borel_measurable
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedWholeCode rule)))
      (fun marks => actualFiniteAnnealedWholeResponse rule scale scalePositive depth clock kind
        (markedGenerationConfiguration rule marks depth [] true, initial marks)) := by
  have response : @Measurable _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedWholeCode rule)))
      (actualFiniteAnnealedWholeResponse rule scale scalePositive depth clock kind) :=
    @measurable_of_finite _ _ inferInstance (borel (ProbabilityMeasure (ActualAnnealedWholeCode rule))) inferInstance inferInstance _
  exact @Measurable.comp _ _ _ inferInstance inferInstance (borel (ProbabilityMeasure (ActualAnnealedWholeCode rule))) _ _
    response ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

end
end IGSIII34.Spectral

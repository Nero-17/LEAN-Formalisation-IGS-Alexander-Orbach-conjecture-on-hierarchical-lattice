import IGSIII34.Diffusion.OriginalJointCompactPathEncodingContinuous
import IGSIII34.Spectral.Collars.ActualFiniteIntrinsicJointResponse
import Mathlib.Probability.Kernel.Composition.CompMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion IGSIII34.ResistanceLimit MeasureTheory ProbabilityTheory

def actualFiniteOriginalJointFallback : OriginalJointCompactSpace :=
  originalJointCompactPathEncoding (fun _ => ()) (fun _ => diracProba ())
    ⟨⟨fun _ _ => ()⟩, continuous_path_cadlag_completion20261011 _ continuous_const⟩

variable (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)

/-- The actual finite conditional probability retains the original normalized
chemical metric, both original physical masses and terminals, and the ENTIRE
original finite cadlag path in the common-isometric-embedding joint space. -/
def actualFiniteOriginalJointResponse
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (input : Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices) :
    ProbabilityMeasure OriginalJointCompactSpace := by
  classical
  if crossing : (rule.generation depth).network.crosses input.1 = true then
    if positive : 0 < clock input.1 then
      exact (actualFiniteAnnealedCanonicalPathLaw rule scale scalePositive depth input.1 crossing
        input.2 (clock input.1) positive kind).map
        (originalJointCompactPathEncoding_continuous
          (actualFiniteIntrinsicJointMark rule scale scalePositive depth input.1 crossing)
          (actualFiniteIntrinsicJointMass rule scale scalePositive depth input.1 crossing)).measurable.aemeasurable
    else exact diracProba actualFiniteOriginalJointFallback
  else exact diracProba actualFiniteOriginalJointFallback

theorem actualFiniteOriginalJointResponse_crossing
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (configuration : Configuration (rule.generation depth).edges)
    (crossing : (rule.generation depth).network.crosses configuration = true)
    (initial : Fin (rule.generation depth).vertices) (positive : 0 < clock configuration) :
    actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind (configuration, initial) =
      (actualFiniteAnnealedCanonicalPathLaw rule scale scalePositive depth configuration crossing
        initial (clock configuration) positive kind).map
        (originalJointCompactPathEncoding_continuous
          (actualFiniteIntrinsicJointMark rule scale scalePositive depth configuration crossing)
          (actualFiniteIntrinsicJointMass rule scale scalePositive depth configuration crossing)).measurable.aemeasurable := by
  classical
  simp only [actualFiniteOriginalJointResponse, dif_pos crossing, dif_pos positive]

def actualFiniteOriginalJointConfigurationKernel
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3) :
    Kernel (Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices)
      OriginalJointCompactSpace :=
  Kernel.ofFunOfCountable (fun input => (actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind input : Measure _))

instance actualFiniteOriginalJointConfigurationKernel_markov
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3) :
    IsMarkovKernel (actualFiniteOriginalJointConfigurationKernel rule scale scalePositive depth clock kind) := by
  constructor
  intro input
  change IsProbabilityMeasure (actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind input : Measure _)
  infer_instance

def actualFiniteOriginalJointEnvironmentKernel
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    Kernel (((List (Fin rule.edges) × Bool) → Configuration rule.edges)) OriginalJointCompactSpace :=
  (actualFiniteOriginalJointConfigurationKernel rule scale scalePositive depth clock kind).comap
    (fun marks => (markedGenerationConfiguration rule marks depth [] true, initial marks))
    ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

instance actualFiniteOriginalJointEnvironmentKernel_markov
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    IsMarkovKernel (actualFiniteOriginalJointEnvironmentKernel rule scale scalePositive depth clock kind initial initialMeasurable) := by
  unfold actualFiniteOriginalJointEnvironmentKernel
  infer_instance

theorem actualFiniteOriginalJointResponse_measurable
    (clock : Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Fin (rule.generation depth).vertices)
    (initialMeasurable : Measurable initial) :
    Measurable (fun marks => actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind
      (markedGenerationConfiguration rule marks depth [] true, initial marks)) :=
  (measurable_of_finite (actualFiniteOriginalJointResponse rule scale scalePositive depth clock kind)).comp
    ((markedGenerationConfiguration_measurable rule depth [] true).prodMk initialMeasurable)

end
end IGSIII34.Spectral

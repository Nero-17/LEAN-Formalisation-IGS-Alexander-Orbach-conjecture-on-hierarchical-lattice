import IGSIII.Chemical.SubstitutionPaths.WeightedLeafLaw
import IGSIII.Chemical.SubstitutionPaths.CommonPrefixL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability
open scoped Topology ENNReal

noncomputable section

def rawInnovationPrefix20261011 (rule : Rule) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth} → Configuration rule.edges :=
  fun coordinate => marks coordinate.val

@[reducible] def rawInnovationPrefixSigma20261011 (rule : Rule) (depth : ℕ) :
    MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges) :=
  MeasurableSpace.comap (rawInnovationPrefix20261011 rule depth) inferInstance

theorem rawInnovationPrefixSigma_le20261011 (rule : Rule) (depth : ℕ) :
    rawInnovationPrefixSigma20261011 rule depth ≤
      (inferInstance : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges)) := by
  exact (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).comap_le

/-- The actual orthogonal conditional-expectation residual for the raw prefix. -/
def rawPrefixResidual20261011 (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint) →L[ℝ]
      Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  ContinuousLinearMap.id ℝ _ -
    (lpMeas ℝ ℝ (rawInnovationPrefixSigma20261011 rule depth) 2
      (independentInnovationLaw rule p positive belowOne fixedPoint)).subtypeL.comp
        (condExpL2 ℝ ℝ (rawInnovationPrefixSigma_le20261011 rule depth))

theorem markedObservableLp_rawPrefix_measurable20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    AEStronglyMeasurable[rawInnovationPrefixSigma20261011 rule (depth + 1)]
      (markedObservableLp rule p positive belowOne fixedPoint depth [] true response)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have represented : (fun marks => response (markedGenerationConfiguration rule marks depth [] true)) =
      (response ∘ generationConfigurationFromPrefix rule depth) ∘ rawInnovationPrefix20261011 rule (depth + 1) := by
    funext marks
    exact congrArg response (markedGenerationConfiguration_fromPrefix rule depth marks).symm
  have measurable : Measurable[rawInnovationPrefixSigma20261011 rule (depth + 1)]
      (fun marks => response (markedGenerationConfiguration rule marks depth [] true)) := by
    rw [represented]
    exact ((measurable_of_countable response).comp
      (generationConfigurationFromPrefix_measurable rule depth)).comp
        (comap_measurable _)
  exact measurable.stronglyMeasurable.aestronglyMeasurable.congr
    (markedObservableLp_ae rule p positive belowOne fixedPoint depth [] true response).symm

theorem rawPrefixResidual_le_approximation20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    (value approximation : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (measurable : AEStronglyMeasurable[rawInnovationPrefixSigma20261011 rule depth]
      approximation (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth value‖ ≤
      ‖value - approximation‖ := by
  letI : Fact (rawInnovationPrefixSigma20261011 rule depth ≤
      (inferInstance : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges))) :=
    ⟨rawInnovationPrefixSigma_le20261011 rule depth⟩
  have member : approximation ∈ lpMeas ℝ ℝ (rawInnovationPrefixSigma20261011 rule depth) 2
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr measurable
  change ‖value - (lpMeas ℝ ℝ (rawInnovationPrefixSigma20261011 rule depth) 2
    (independentInnovationLaw rule p positive belowOne fixedPoint)).starProjection value‖ ≤ _
  rw [Submodule.starProjection_minimal]
  have lower : BddBelow (Set.range (fun point : lpMeas ℝ ℝ
      (rawInnovationPrefixSigma20261011 rule depth) 2
      (independentInnovationLaw rule p positive belowOne fixedPoint) =>
        ‖value - (point : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨point, rfl⟩
    exact norm_nonneg _
  exact ciInf_le lower ⟨approximation, member⟩

theorem rawPrefixResidual_zero_of_measurable20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (measurable : AEStronglyMeasurable[rawInnovationPrefixSigma20261011 rule depth]
      value (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth value = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [sub_self, norm_zero] using
    rawPrefixResidual_le_approximation20261011 rule p positive belowOne fixedPoint depth value value measurable)
      (norm_nonneg _)

theorem rawPrefixResidual_bound_of_limit20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (bound : ℝ)
    (sequence : ℕ → Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (limit : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (convergence : Tendsto sequence atTop (𝓝 limit))
    (bounded : ∀ᶠ index in atTop,
      ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth (sequence index)‖ ^ 2 ≤ bound) :
    ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth limit‖ ^ 2 ≤ bound := by
  exact le_of_tendsto
    (((rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth).continuous.tendsto limit).norm.pow 2 |>.comp convergence)
      bounded

theorem rawPrefixResidual_bound_of_scalar_limit20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (bound amplitude : ℝ)
    (amplitudeAtLeastOne : 1 ≤ amplitude)
    (sequence : ℕ → Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (convergence : Tendsto sequence atTop (𝓝 (amplitude • value)))
    (bounded : ∀ᶠ index in atTop,
      ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth (sequence index)‖ ^ 2 ≤ bound) :
    ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth value‖ ^ 2 ≤ bound := by
  have scaled := rawPrefixResidual_bound_of_limit20261011 rule p positive belowOne fixedPoint depth
    bound sequence (amplitude • value) convergence bounded
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ amplitude), mul_pow] at scaled
  have squareAtLeastOne : 1 ≤ amplitude ^ 2 := by nlinarith
  have comparison := mul_le_mul_of_nonneg_right squareAtLeastOne
    (sq_nonneg ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth value‖)
  have comparison' : ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth value‖ ^ 2 ≤
      amplitude ^ 2 * ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint depth value‖ ^ 2 := by
    simpa only [one_mul] using comparison
  exact comparison'.trans scaled

end
end IGSIII.Chemical.Substitution

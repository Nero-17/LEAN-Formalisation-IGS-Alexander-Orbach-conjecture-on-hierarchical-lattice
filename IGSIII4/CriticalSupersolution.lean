import IGSIII4.SupersolutionGrowth
import IGSIII4.CriticalDomination
import IGSIII4.PositiveRepresentative
import IGSIII4.SupersolutionRigidity

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII34.Percolation

theorem supersolution_growth_lower_bound (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ value marks)
    (meanPositive : 0 < ∫ marks, value marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    {factor : ℝ} (factorPositive : 0 < factor)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ factor * value marks) : accepted.growth ≤ factor := by
  obtain ⟨representative, representativeMeasurable, representativePositive, _same,
    representativeIntegrable, representativeInverseIntegrable, inverseMeanPositive, representativeSupersolution⟩ :=
    supersolution_positive_representative rule classicalRule probability positive belowOne fixedPoint value
      measurable integrable nonnegative meanPositive factorPositive supersolution
  exact supersolution_growth_lower_bound_positive_input rule probability positive belowOne fixedPoint accepted
    representative representativeMeasurable representativePositive representativeIntegrable
    representativeInverseIntegrable inverseMeanPositive factorPositive representativeSupersolution

theorem critical_supersolution_domination (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ value marks)
    (meanPositive : 0 < ∫ marks, value marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ accepted.growth * value marks) :
    ∃ scalar : ℝ, 0 < scalar ∧
      ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
        accepted.field marks ≤ scalar * value marks := by
  obtain ⟨representative, representativeMeasurable, representativePositive, same,
    representativeIntegrable, representativeInverseIntegrable, inverseMeanPositive, representativeSupersolution⟩ :=
    supersolution_positive_representative rule classicalRule probability positive belowOne fixedPoint value
      measurable integrable nonnegative meanPositive (zero_lt_one.trans accepted.growthAboveOne) supersolution
  refine ⟨∫ marks, (representative marks : ℝ)⁻¹
    ∂independentInnovationLaw rule probability positive belowOne fixedPoint, inverseMeanPositive, ?_⟩
  have domination := critical_supersolution_domination_positive_input rule probability positive belowOne fixedPoint
    accepted representative representativeMeasurable representativePositive representativeIntegrable
    representativeInverseIntegrable inverseMeanPositive representativeSupersolution
  filter_upwards [domination, same] with marks bound identity
  rwa [identity] at bound

theorem critical_supersolution_rigidity (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ value marks)
    (meanPositive : 0 < ∫ marks, value marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ accepted.growth * value marks) :
    ∃ scalar : ℝ, 0 < scalar ∧
      value =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
        fun marks => scalar * accepted.field marks := by
  exact supersolution_rigidity_of_domination
    (independentInnovationLaw rule probability positive belowOne fixedPoint) (electricalTransfer rule) accepted.growth
    (fun first second same => electricalTransfer_congr_ae rule probability positive belowOne fixedPoint same)
    (fun scalar scalarNonnegative _value nonnegative =>
      electricalTransfer_scale_ae rule probability positive belowOne fixedPoint nonnegative scalarNonnegative)
    (fun _first _second firstNonnegative secondNonnegative =>
      electricalTransfer_superadditive_ae rule probability positive belowOne fixedPoint firstNonnegative secondNonnegative)
    accepted.field accepted.fieldMeasurable accepted.fieldIntegrable accepted.fieldPositive accepted.fieldEquation
    (fun value measurable integrable nonnegative meanPositive supersolution =>
      critical_supersolution_domination rule classicalRule probability positive belowOne fixedPoint accepted
        value measurable integrable nonnegative meanPositive supersolution)
    value measurable integrable nonnegative meanPositive supersolution

/-- Lemma critical-supersolution, for the actual electrical transfer of the
original innovation tree, conditional only on the accepted Section 3 results. -/
theorem critical_supersolution (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ value marks)
    (meanPositive : 0 < ∫ marks, value marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    {factor : ℝ} (factorPositive : 0 < factor)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ factor * value marks) :
    accepted.growth ≤ factor ∧ (factor = accepted.growth →
      ∃ scalar : ℝ, 0 < scalar ∧
        value =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
          fun marks => scalar * accepted.field marks) := by
  refine ⟨supersolution_growth_lower_bound rule classicalRule probability positive belowOne fixedPoint accepted
    value measurable integrable nonnegative meanPositive factorPositive supersolution, ?_⟩
  intro equality
  rw [equality] at supersolution
  exact critical_supersolution_rigidity rule classicalRule probability positive belowOne fixedPoint accepted
    value measurable integrable nonnegative meanPositive supersolution

end
end IGSIII4

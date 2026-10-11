import IGSIII4.InnovationFiltration
import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII34.Percolation

/-- Precisely the Section 3 dependencies explicitly accepted by the user.
`conditionalLower` and `meanLower` are the lower sandwich and its mean
consequence in Lemma electrical-sandwich, on the actual marked generations.
No Section 4 supersolution, strict comparison, or core-clock assertion is a field. -/
structure AcceptedElectricalSectionThree (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) where
  growth : ℝ
  growthAboveOne : 1 < growth
  field : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ
  fieldMeasurable : Measurable field
  fieldIntegrable : Integrable field (independentInnovationLaw rule probability positive belowOne fixedPoint)
  fieldPositive : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 < field marks
  fieldMeanOne : (∫ marks, field marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint) = 1
  fieldEquation : electricalTransfer rule field
    =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint] fun marks => growth * field marks
  conditionalLower : ∀ depth : ℕ,
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      growth ^ (depth + 1) *
        (condExp (innovationFiltration rule (depth + 1))
          (independentInnovationLaw rule probability positive belowOne fixedPoint) field) marks ≤
      unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)
  meanLower : ∀ depth : ℕ, growth ^ (depth + 1) ≤
    ∫ marks, unitConfigurationResistance (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true)
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint

end
end IGSIII4

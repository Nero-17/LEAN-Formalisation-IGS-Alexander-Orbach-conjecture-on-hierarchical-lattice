import IGSIII4.ActualCoreClock
import IGSIII34.Percolation.Continuation.SectionFourDependency
import IGSIII34.Percolation.Continuation.NaturalMeanUpperCompletion
import IGSIII34.Resistance.ActualTerminalCorePruningCompletion

/-! The former Section 3 interfaces are certificates constructed from actual
Section 3 proofs. They are not hypotheses of the integrated public results. -/
set_option autoImplicit false

namespace IGSIII4
noncomputable section
open Universality MeasureTheory IGSIII34.Percolation

theorem exists_natural_section_four_mean_upper
    (rule : Rule) (classicalRule : rule.Classical) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (natural : NaturalResistanceCompletion rule probability positive belowOne fixedPoint) :
    Nonempty (AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint
      (naturalSectionFourElectrical rule probability positive belowOne fixedPoint natural)) := by
  obtain ⟨constant, constantPositive, meanUpper⟩ :=
    natural_electrical_mean_upper_completion rule classicalRule probability positive belowOne fixedPoint natural
  exact ⟨⟨constant, constantPositive, meanUpper⟩⟩

def naturalSectionFourMeanUpper
    (rule : Rule) (classicalRule : rule.Classical) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (natural : NaturalResistanceCompletion rule probability positive belowOne fixedPoint) :
    AcceptedResistanceMeanUpperSectionThree rule probability positive belowOne fixedPoint
      (naturalSectionFourElectrical rule probability positive belowOne fixedPoint natural) :=
  Classical.choice (exists_natural_section_four_mean_upper rule classicalRule probability
    positive belowOne fixedPoint natural)

theorem actual_section_four_core_pruning
    (rule : Rule) (classicalRule : rule.Classical) : AcceptedCorePruningSectionThree rule :=
  classical_actual_core_pruning_section_three_completion rule classicalRule

end
end IGSIII4

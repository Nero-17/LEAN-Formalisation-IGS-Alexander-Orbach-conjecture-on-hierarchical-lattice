import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion
import IGSIII34.Percolation.GenerationMean

set_option autoImplicit false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Chemical.Substitution

theorem natural_electrical_mean_upper_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ depth,
      (∫ marks, unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ constant * natural.growth ^ (depth + 1) := by
  obtain ⟨constant, constantPositive, growthBounds, _, _⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  refine ⟨constant⁻¹, inv_pos.mpr constantPositive, ?_⟩
  intro depth
  calc
    _ = ∫ marks, electricalIteration rule marks (depth + 1) []
        ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
      apply integral_congr_ae
      filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks crossing
      exact markedGeneration_resistance_eq_iteration rule marks crossing depth []
    _ = (electricalOrbitScale rule p positive belowOne fixedPoint (depth + 1) : ℝ) :=
      (electricalOrbitScale_eq_actual_mean rule classicalRule p positive belowOne fixedPoint (depth + 1)).symm
    _ ≤ _ := (growthBounds (depth + 1)).2

end
end IGSIII34.Percolation

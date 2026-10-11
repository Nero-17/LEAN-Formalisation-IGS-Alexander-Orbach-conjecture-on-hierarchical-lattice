import IGSIII34.Percolation.Continuation.ElectricalAddressEnvelope

set_option autoImplicit false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory
open scoped ENNReal

theorem actual_terminal_resistance_envelopes_fixed_cluster
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (power : ℕ) (powerPositive : 0 < power) :
    ∃ functions : List (Fin rule.edges) → Bool →
        (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧
        (∀ address opened, Measurable (functions address opened)) ∧
        (∀ address opened, eLpNorm (functions address opened) power
          (independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound) ∧
        ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
          ∀ address opened depth,
          unitConfigurationResistance (rule.generation depth).network
            (markedGenerationConfiguration rule marks depth address opened) / growth ^ (depth + 1) ≤
              functions address opened marks := by
  obtain ⟨envelope, bound, finite, properties, bounds⟩ :=
    electricalIteration_exists_uniform_address_envelope_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership power powerPositive
  refine ⟨fun address _ => envelope address, bound, finite,
    fun address _ => (properties address).1, fun address _ => (properties address).2.2.2, ?_⟩
  filter_upwards [bounds, independentInnovationLaw_crosses rule p positive belowOne fixedPoint]
    with marks bounds crossing
  intro address opened depth
  cases opened with
  | false =>
    have doesNotCross : (rule.generation depth).network.crosses
        (markedGenerationConfiguration rule marks depth address false) ≠ true := by
      rw [markedGenerationConfiguration_crosses rule marks crossing]
      decide
    rw [unitConfigurationResistance, electricalCell_eq_zero_of_not_crosses _ _ doesNotCross, zero_div]
    exact (properties address).2.2.1 marks
  | true =>
    rw [markedGeneration_resistance_eq_iteration rule marks crossing]
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using bounds address (depth + 1)

end
end IGSIII34.ResistanceLimit

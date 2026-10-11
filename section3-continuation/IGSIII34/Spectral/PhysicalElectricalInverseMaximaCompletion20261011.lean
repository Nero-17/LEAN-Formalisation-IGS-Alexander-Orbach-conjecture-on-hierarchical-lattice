import IGSIII34.Spectral.ElectricalInverseMaximaCompletion20261011
import IGSIII34.ResistanceLimit.ActualHarmonic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open IGSIII34.Percolation IGSIII34.ResistanceLimit MeasureTheory Filter
open scoped Topology

theorem natural_physical_electrical_field_scaling_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address : List (Fin rule.edges),
        electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) address marks =
          natural.amplitude * electricalField rule p positive belowOne fixedPoint natural.field address marks := by
  apply ae_all_iff.mpr
  intro address
  have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae
    (Lp.coeFn_smul natural.amplitude natural.field)
  simpa only [electricalField, Pi.smul_apply, smul_eq_mul] using shifted

theorem natural_physical_stationary_harmonic_typical_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) marks := by
  apply stationaryHarmonicTypical_ae rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
  · filter_upwards [natural.fieldPositive, Lp.coeFn_smul natural.amplitude natural.field] with marks positiveField scalar
    rw [scalar]
    exact mul_pos (zero_lt_one.trans_le natural.amplitudeLower) positiveField
  · rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 natural.growth
      natural.amplitude (zero_le_one.trans natural.amplitudeLower), natural.fieldFixed]

/-- The electrical field used by the physical unit-edge resistance limit
includes its actual amplitude. Its inverse maxima obey the same estimate
because this amplitude is at least one. -/
theorem physical_electrical_inverse_alladdress_subexponential_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ threshold : ℕ, ∀ address : List (Fin rule.edges),
        threshold ≤ address.length →
        (electricalField rule p positive belowOne fixedPoint (natural.amplitude • natural.field) address marks)⁻¹ ≤
          slack^address.length := by
  filter_upwards [actual_electrical_inverse_alladdress_subexponential_completion20261011
      rule p positive belowOne fixedPoint natural,
    natural_physical_electrical_field_scaling_completion20261011 rule p positive belowOne fixedPoint natural,
    electricalField_positive rule p positive belowOne fixedPoint natural.field natural.fieldPositive]
    with marks maxima scaling positiveField
  intro slack greater
  obtain ⟨threshold, estimates⟩ := maxima slack greater
  refine ⟨threshold, ?_⟩
  intro address after
  rw [scaling address, mul_inv_rev]
  have amplitudeInverseBound : natural.amplitude⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (zero_lt_one.trans_le natural.amplitudeLower)).mpr natural.amplitudeLower
  exact (mul_le_mul_of_nonneg_left amplitudeInverseBound (inv_nonneg.mpr (positiveField address).le)).trans
    (by simpa only [mul_one] using estimates address after)

end
end IGSIII34.Spectral

import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion
import IGSIII34.Percolation.ElectricalSandwich

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Probability
open IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory Filter
open scoped _root_.Topology

/-- The physical amplitude of the SAME natural mean-one electrical field
lies in the manuscript interval [1, E X⁻¹]. -/
theorem natural_electrical_amplitude_bounds
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    1 ≤ natural.amplitude ∧ natural.amplitude ≤
      ∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  have inverseIntegrable : Integrable (fun marks => (natural.field marks)⁻¹)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    simpa only [Real.rpow_neg_one] using natural.fieldMoments (-1)
  have inversePositive := inverse_mean_positive
    (independentInnovationLaw rule p positive belowOne fixedPoint) natural.field natural.fieldPositive inverseIntegrable
  obtain ⟨constant, constantPositive, growthBounds, membership, endpointFixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  have endpointLimit := electricalOrbitLp_tendsto_ae_fixed_cluster rule classicalRule p positive belowOne fixedPoint
    constant natural.growth constantPositive (zero_lt_one.trans natural.aboveOne) growthBounds
    (natural.amplitude • natural.field) endpointFixed membership
  have conditionalLimit := coordinatePrefixFiltration_condExp_tendsto
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
    (independentInnovationLaw rule p positive belowOne fixedPoint) natural.field
    (Lp.stronglyMeasurable natural.field) ((Lp.memLp natural.field).integrable (by norm_num))
  have sandwiches := ae_all_iff.mpr (electricalOrbit_conditional_fixed_sandwich
    rule p positive belowOne fixedPoint natural.growth (zero_lt_one.trans natural.aboveOne).le
    natural.field natural.fieldPositive natural.fieldFixed natural.fieldMeanOne inverseIntegrable
    (∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) inversePositive rfl)
  have scalarBound : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      natural.amplitude ≤ ∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
    filter_upwards [endpointLimit, conditionalLimit, sandwiches, Lp.coeFn_smul natural.amplitude natural.field,
      natural.fieldPositive] with marks endpoint conditional bounds scalar fieldPositive
    have inequality := le_of_tendsto_of_tendsto (endpoint.comp (tendsto_add_atTop_nat 1))
      ((conditional.comp (tendsto_add_atTop_nat 1)).const_mul
        (∫ marks, (natural.field marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint))
      (Eventually.of_forall (fun depth => (bounds depth).2))
    rw [scalar] at inequality
    apply (mul_le_mul_iff_right₀ fieldPositive).mp
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using inequality
  obtain ⟨marks, amplitudeUpper⟩ := scalarBound.exists
  exact ⟨natural.amplitudeLower, amplitudeUpper⟩

end
end IGSIII34.Diffusion

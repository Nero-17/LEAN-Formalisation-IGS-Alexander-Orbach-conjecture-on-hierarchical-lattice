import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion
import IGSIII34.Spectral.MassFieldMaxima
import Mathlib.Topology.Instances.Rat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open IGSIII34.Percolation MeasureTheory Filter
open scoped ENNReal Topology

theorem actual_electrical_inverse_uniform_nat_moment_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (power : ℕ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ address : List (Fin rule.edges),
      (∫⁻ marks, ENNReal.ofReal ((electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹)^power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ENNReal.ofReal bound := by
  have rootIntegrable : Integrable (fun marks => (natural.field marks)⁻¹^power)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast] using natural.fieldMoments (-(power : ℝ))
  let rootMean := ∫ marks, (natural.field marks)⁻¹^power ∂independentInnovationLaw rule p positive belowOne fixedPoint
  refine ⟨max 1 rootMean, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro address
  have positiveField := electricalField_positive rule p positive belowOne fixedPoint natural.field natural.fieldPositive
  have shiftedIntegrable : Integrable
      (fun marks => (electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹^power)
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).integrable_comp
      ((Lp.stronglyMeasurable natural.field).measurable.inv.pow_const power).aestronglyMeasurable |>.mpr rootIntegrable
  have shiftedMean : (∫ marks,
      (electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹^power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) = rootMean := by
    have transport := integral_map_of_stronglyMeasurable
      (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
      (innovationTreeShift_measurable rule address)
      ((Lp.stronglyMeasurable natural.field).measurable.inv.pow_const power).stronglyMeasurable
    rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq] at transport
    exact transport.symm
  have integrandEquality : (fun marks =>
      ENNReal.ofReal ((electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹)^power) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => ENNReal.ofReal ((electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹^power) := by
    filter_upwards [positiveField] with marks positives
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr (positives address).le)]
  rw [lintegral_congr_ae integrandEquality,
    ← ofReal_integral_eq_lintegral_ofReal shiftedIntegrable
      (positiveField.mono (fun marks positives => pow_nonneg (inv_nonneg.mpr (positives address).le) power)),
    shiftedMean]
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- Actual electrical conductance factors have subexponential maxima over
all physical addresses, with every slack on one event of probability one.
The inverse moments are proved by the natural eigenfield construction. -/
theorem actual_electrical_inverse_alladdress_subexponential_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ growth : ℝ, 1 < growth → ∃ threshold : ℕ, ∀ address : List (Fin rule.edges),
        threshold ≤ address.length →
        (electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹ ≤ growth^address.length := by
  have positiveField := electricalField_positive rule p positive belowOne fixedPoint natural.field natural.fieldPositive
  have rationalBound (growth : ℚ) :
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        1 < (growth : ℝ) → ∃ threshold : ℕ, ∀ address : List (Fin rule.edges),
          threshold ≤ address.length →
          (electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹ ≤ (growth : ℝ)^address.length := by
    by_cases greater : 1 < (growth : ℝ)
    · have bound := ae_mass_field_descendant_exponential
        (independentInnovationLaw rule p positive belowOne fixedPoint) rule.edges
        (fun address (_ : OrientedState) marks => (electricalField rule p positive belowOne fixedPoint natural.field address marks)⁻¹)
        (fun address _ => (electricalField_measurable rule p positive belowOne fixedPoint natural.field address).inv.aestronglyMeasurable)
        (positiveField.mono (fun marks positives address _ => inv_nonneg.mpr (positives address).le))
        (fun power => by
          obtain ⟨bound, boundPositive, moments⟩ := actual_electrical_inverse_uniform_nat_moment_completion
            rule p positive belowOne fixedPoint natural power
          exact ⟨bound, boundPositive, fun address _ => moments address⟩)
        (growth : ℝ) greater
      exact bound.mono (fun marks property _ => by
        obtain ⟨threshold, estimates⟩ := property
        exact ⟨threshold, fun address after => estimates address .connected after⟩)
    · exact Eventually.of_forall (fun _ impossible => (greater impossible).elim)
  filter_upwards [ae_all_iff.mpr rationalBound] with marks rationalBounds
  intro growth greater
  obtain ⟨rational, aboveOne, belowGrowth⟩ := exists_rat_btwn greater
  obtain ⟨threshold, estimates⟩ := rationalBounds rational aboveOne
  refine ⟨threshold, ?_⟩
  intro address after
  exact (estimates address after).trans
    (pow_le_pow_left₀ (zero_lt_one.trans aboveOne).le belowGrowth.le _)

end
end IGSIII34.Spectral

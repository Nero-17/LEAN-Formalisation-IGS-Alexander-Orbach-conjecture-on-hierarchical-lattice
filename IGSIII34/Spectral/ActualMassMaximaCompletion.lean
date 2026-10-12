import IGSIII34.Spectral.MassFieldMaxima
import Mathlib.Topology.Instances.Rat

/-! All-address subexponential bounds for the actual oriented critical mass
field. The full field, positivity, inactive convention and joint B splitting
are constructed on the original innovation law, not supplied as hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

theorem exists_actual_mass_field_subexponential
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ limit : List (Fin rule.edges) → OrientedState →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ address marks, limit address .inactive marks = 0) ∧
      (∀ address marks, limit address .both marks =
        limit address .sourceOnly marks + limit address .targetOnly marks) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address parent,
        0 ≤ limit address parent marks ∧
        Tendsto (fun depth => markedOrientedVertexMass rule marks depth address parent /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 (limit address parent marks)) ∧
        (parent = .connected → 0 < limit address parent marks)) ∧
      (∀ address parent, AEStronglyMeasurable (limit address parent)
        (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
      (∀ power : ℕ, ∃ bound : ℝ, 0 < bound ∧ ∀ address parent,
        (∫⁻ marks, ENNReal.ofReal (limit address parent marks) ^ power
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ENNReal.ofReal bound) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ growth : ℝ, 1 < growth → ∃ threshold : ℕ, ∀ address parent,
          threshold ≤ address.length → limit address parent marks ≤ growth ^ address.length := by
  obtain ⟨limit, inactive, split, convergence, measurable, moments⟩ :=
    exists_actual_mass_field_all_nat_moments classicalRule p positive belowOne fixedPoint
  refine ⟨limit, inactive, split, convergence, measurable, moments, ?_⟩
  have nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address parent, 0 ≤ limit address parent marks :=
    convergence.mono (fun _ properties address parent => (properties address parent).1)
  have rationalBound : ∀ growth : ℚ, ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      1 < (growth : ℝ) → ∃ threshold : ℕ, ∀ address parent,
        threshold ≤ address.length → limit address parent marks ≤ (growth : ℝ) ^ address.length := by
    intro growth
    by_cases greater : 1 < (growth : ℝ)
    · exact (ae_mass_field_descendant_exponential
        (independentInnovationLaw rule p positive belowOne fixedPoint) rule.edges limit
        measurable nonnegative moments (growth : ℝ) greater).mono
          (fun _ bounded _ => bounded)
    · exact Filter.Eventually.of_forall (fun _ impossible => (greater impossible).elim)
  filter_upwards [ae_all_iff.mpr rationalBound] with marks bounded
  intro growth greater
  obtain ⟨rational, aboveOne, belowGrowth⟩ := exists_rat_btwn greater
  obtain ⟨threshold, estimates⟩ := bounded rational aboveOne
  refine ⟨threshold, ?_⟩
  intro address parent after
  exact (estimates address parent after).trans
    (pow_le_pow_left₀ (zero_lt_one.trans aboveOne).le belowGrowth.le _)

end
end IGSIII34.Spectral

import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Order.Iterate
import Mathlib.Data.Set.Function

/-! A fixed-point construction by decreasing, bounded iterates.  This is a
component of the special monotone-operator route and does not invoke Schauder.
The lower bound on the actual orbit remains a mathematical obligation. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Filter
open scoped Topology

noncomputable section

theorem exists_fixedPoint_of_decreasing_bounded_iterates {Sample : Type*}
    (map : (Sample → ℝ) → (Sample → ℝ)) (start lower : Sample → ℝ)
    (monotone : Monotone map) (continuous : Continuous map)
    (firstStep : map start ≤ start)
    (lowerBound : ∀ depth : ℕ, lower ≤ map^[depth] start) :
    ∃ fixed : Sample → ℝ, map fixed = fixed ∧ lower ≤ fixed ∧ fixed ≤ start := by
  have steps : ∀ depth : ℕ, map^[depth + 1] start ≤ map^[depth] start := by
    intro depth
    induction depth with
    | zero => simpa using firstStep
    | succ depth inductionHypothesis =>
        simpa only [Function.iterate_succ_apply'] using monotone inductionHypothesis
  have decreasing (sample : Sample) : Antitone (fun depth : ℕ => map^[depth] start sample) :=
    antitone_nat_of_succ_le (fun depth => steps depth sample)
  have bounded (sample : Sample) : BddBelow (Set.range (fun depth : ℕ => map^[depth] start sample)) :=
    ⟨lower sample, by rintro _ ⟨depth, rfl⟩; exact lowerBound depth sample⟩
  have convergence : Tendsto (fun depth : ℕ => map^[depth] start) atTop
      (𝓝 (fun sample => ⨅ depth : ℕ, map^[depth] start sample)) := by
    apply tendsto_pi_nhds.mpr
    intro sample
    exact tendsto_atTop_ciInf (decreasing sample) (bounded sample)
  refine ⟨fun sample => ⨅ depth : ℕ, map^[depth] start sample,
    isFixedPt_of_tendsto_iterate convergence continuous.continuousAt, ?_, ?_⟩
  · intro sample
    exact le_ciInf (fun depth => lowerBound depth sample)
  · intro sample
    exact ciInf_le (bounded sample) 0

/-- A uniformly comparable invariant family yields a positive fixed point by
descending from its lower envelope.  All comparisons here are pointwise.
For random functions an almost-everywhere quotient or a common null-set bridge
must be supplied before applying this theorem. -/
theorem exists_positive_fixedPoint_of_comparable_invariant_family {Sample : Type*}
    (map : (Sample → ℝ) → (Sample → ℝ)) (family : Set (Sample → ℝ))
    {anchor : Sample → ℝ} {constant : ℝ}
    (anchorMember : anchor ∈ family) (anchorPositive : ∀ sample, 0 < anchor sample)
    (constantPositive : 0 < constant)
    (monotone : Monotone map) (continuous : Continuous map)
    (homogeneous : ∀ function : Sample → ℝ,
      map (fun sample => constant⁻¹ * function sample) =
        (fun sample => constant⁻¹ * map function sample))
    (mapsTo : Set.MapsTo map family family) (onto : Set.SurjOn map family family)
    (comparable : ∀ first ∈ family, ∀ second ∈ family, ∀ sample,
      first sample ≤ constant * second sample) :
    ∃ fixed : Sample → ℝ, map fixed = fixed ∧
      (∀ sample, 0 < fixed sample) ∧ fixed ≤ anchor := by
  letI : Nonempty family := ⟨⟨anchor, anchorMember⟩⟩
  have memberLower (member : family) (sample : Sample) :
      constant⁻¹ * anchor sample ≤ member.val sample := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ constantPositive).mpr
    simpa only [mul_comm] using comparable anchor anchorMember member.val member.property sample
  have bounded (sample : Sample) : BddBelow (Set.range (fun member : family => member.val sample)) :=
    ⟨constant⁻¹ * anchor sample, by rintro _ ⟨member, rfl⟩; exact memberLower member sample⟩
  let envelope : Sample → ℝ := fun sample => ⨅ member : family, member.val sample
  have envelopeLower : (fun sample => constant⁻¹ * anchor sample) ≤ envelope := by
    intro sample
    exact le_ciInf (fun member => memberLower member sample)
  have envelopeUpper (member : family) : envelope ≤ member.val := by
    intro sample
    exact ciInf_le (bounded sample) member
  have firstStep : map envelope ≤ envelope := by
    intro sample
    apply le_ciInf
    intro member
    obtain ⟨predecessor, predecessorMember, image⟩ := onto member.property
    have comparison := monotone (envelopeUpper ⟨predecessor, predecessorMember⟩) sample
    rwa [image] at comparison
  have scaledIterations : ∀ depth : ℕ,
      map^[depth] (fun sample => constant⁻¹ * anchor sample) =
        (fun sample => constant⁻¹ * map^[depth] anchor sample) := by
    intro depth
    induction depth with
    | zero => rfl
    | succ depth inductionHypothesis =>
        rw [Function.iterate_succ_apply', inductionHypothesis, homogeneous]
        simp only [Function.iterate_succ_apply']
  have lowerBound : ∀ depth : ℕ,
      (fun sample => constant⁻¹ * (constant⁻¹ * anchor sample)) ≤ map^[depth] envelope := by
    intro depth sample
    have anchorIterateMember := mapsTo.iterate depth anchorMember
    have comparison := (monotone.iterate depth) envelopeLower sample
    rw [scaledIterations] at comparison
    exact (mul_le_mul_of_nonneg_left
      (memberLower ⟨map^[depth] anchor, anchorIterateMember⟩ sample)
      (inv_pos.mpr constantPositive).le).trans comparison
  obtain ⟨fixed, fixedPoint, lower, upper⟩ :=
    exists_fixedPoint_of_decreasing_bounded_iterates map envelope
      (fun sample => constant⁻¹ * (constant⁻¹ * anchor sample)) monotone continuous firstStep lowerBound
  refine ⟨fixed, fixedPoint, ?_, upper.trans (envelopeUpper ⟨anchor, anchorMember⟩)⟩
  intro sample
  exact (mul_pos (inv_pos.mpr constantPositive)
    (mul_pos (inv_pos.mpr constantPositive) (anchorPositive sample))).trans_le (lower sample)

end
end IGSIII.Chemical.SmallBall

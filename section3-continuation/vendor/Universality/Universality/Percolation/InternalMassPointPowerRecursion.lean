import Universality.Graph.ClassicalRule
import Universality.Percolation.MassRowLowerBounds
import Universality.Probability.FiniteProductMomentPointBound
import Universality.Percolation.ConditionalMassAtomOrientation
import Universality.Percolation.ConditionalMassObservable

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- Two genuinely live child cells convert a uniform child atom estimate into
an all-order parent atom estimate controlled by the actual parent moment. -/
theorem Classical.internal_mass_point_power_recursion {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hpoint : ∀ (child : LiveState) (size : ℕ), (rule.generation n).network.conditionalInternalMassProbability p
      (child == .connected) true (child == .both) size ≤ bound)
    (state : LiveState) (order size : ℕ) :
    (size : ℝ) ^ order * (rule.generation (n + 1)).network.conditionalInternalMassProbability p
      (state == .connected) true (state == .both) size ≤
      2 ^ (order + 1) * bound *
        (rule.generation (n + 1)).network.conditionalVertexMoment p state order := by
  classical
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric.generation n
  have hpositive : 0 < (rule.generation n).network.reliability p := by
    rwa [rule.generation_fixed_point p hfixed n]
  have hless : (rule.generation n).network.reliability p < 1 := by
    rwa [rule.generation_fixed_point p hfixed n]
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ := Finset.one_lt_card.mp
    (show 1 < rule.network.sourceIncidentEdges.card by
      have := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
      omega)
  have hchildPoint (coarse : Configuration rule.edges) (edge : Fin rule.edges)
      (hincident : edge ∈ rule.network.sourceIncidentEdges) (target : ℕ) :
      (∑ cell : Configuration (rule.generation n).edges,
        if (rule.generation n).network.internalStateMass
          (rule.network.orientedChildState true (state == .both) coarse edge) cell = target
          then (rule.generation n).network.conditionalCellWeight p (coarse edge) cell else 0) ≤ bound := by
    have hne := rule.network.childState_incident_ne_none state coarse edge hincident
    cases hchild : rule.network.childState state coarse edge with
    | none => exact (hne hchild).elim
    | some child =>
      change (rule.generation n).network.conditionalInternalMassProbability p (coarse edge)
        (rule.network.orientedChildState true (state == .both) coarse edge).sourceSelected
        (rule.network.orientedChildState true (state == .both) coarse edge).targetSelected target ≤ bound
      rw [rule.network.child_conditional_mass_probability (rule.generation n).network symmetry hs ht p
        hpositive hless state child coarse edge hchild]
      exact hpoint child target
  have hbranch (coarse : Configuration rule.edges) := finite_product_two_live_point_bound
    (fun edge cell => (rule.generation n).network.conditionalCellWeight p (coarse edge) cell)
    (fun edge cell => (rule.generation n).network.internalStateMass
      (rule.network.orientedChildState true (state == .both) coarse edge) cell)
    (fun edge cell => (rule.generation n).network.conditionalCellWeight_nonneg hp.le hp'.le _ _)
    (fun edge => (rule.generation n).network.sum_conditionalCellWeight p hpositive hless (coarse edge))
    first second hdistinct.symm bound hbound (hchildPoint coarse first hfirst) (hchildPoint coarse second hsecond)
    (rule.network.internalSelectedMass true (state == .both) coarse) order size
  rw [← (rule.generation (n + 1)).network.conditionalInternalMassObservable_atom p
    (state == .connected) true (state == .both) size]
  change _ ≤ 2 ^ (order + 1) * bound *
    (rule.generation (n + 1)).network.conditionalInternalMassObservable p
      (state == .connected) true (state == .both) (fun mass => (mass : ℝ) ^ order)
  rw [rule.generation_conditionalInternalMassObservable p hp hp' hfixed n,
    rule.generation_conditionalInternalMassObservable p hp hp' hfixed n]
  simp only [mul_ite, mul_one, mul_zero]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro coarse _
  have hscaled := mul_le_mul_of_nonneg_left (hbranch coarse)
    (rule.network.conditionalCellWeight_nonneg hp.le hp'.le (state == .connected) coarse)
  nlinarith

end
end Universality.Rule

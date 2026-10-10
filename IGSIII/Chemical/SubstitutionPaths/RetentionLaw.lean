import IGSIII.Chemical.SubstitutionPaths.FiniteInnovationLaw
import IGSIII.Chemical.SmallBall.Thinning

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Retention under the actual conditional child law

An arbitrary predicate of a connected child configuration becomes a Bernoulli
retention bit with its actual conditional probability. A closed coarse edge
stays closed regardless of its noncrossing child's predicate. The complete
conditional root mixture therefore has the manuscript's reliability thinning
probability, with no independent-child law supplied as a certificate.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Chemical.SmallBall
open scoped BigOperators

noncomputable def connectedRetentionProbability {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ) (retention : Configuration edges → Bool) : ℝ :=
  ∑ configuration, network.conditionalCellWeight p true configuration *
    (if retention configuration then 1 else 0)

theorem connected_retention_bool_fiber {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ)
    (positive : 0 < network.reliability p) (lessOne : network.reliability p < 1)
    (retention : Configuration edges → Bool) (opened : Bool) :
    (∑ configuration, if retention configuration = opened then
      network.conditionalCellWeight p true configuration else 0) =
      bitWeight (connectedRetentionProbability network p retention) opened := by
  classical
  cases opened with
  | true => simp [connectedRetentionProbability, bitWeight]
  | false =>
      have partition :
          (∑ configuration, if retention configuration = false then
            network.conditionalCellWeight p true configuration else 0) +
            connectedRetentionProbability network p retention = 1 := by
        rw [connectedRetentionProbability, ← Finset.sum_add_distrib]
        calc
          _ = ∑ configuration, network.conditionalCellWeight p true configuration := by
            apply Finset.sum_congr rfl
            intro configuration _
            cases retention configuration <;> simp
          _ = 1 := network.sum_conditionalCellWeight p positive lessOne true
      simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
      linarith

theorem conditional_retention_state_fiber {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ)
    (positive : 0 < network.reliability p) (lessOne : network.reliability p < 1)
    (retention : Configuration edges → Bool) (coarse output : Bool) :
    (∑ configuration, if (coarse && retention configuration) = output then
      network.conditionalCellWeight p coarse configuration else 0) =
      ∑ retain : Bool, if (coarse && retain) = output then
        bitWeight (connectedRetentionProbability network p retention) retain else 0 := by
  cases coarse with
  | false =>
      cases output <;> simp [network.sum_conditionalCellWeight p positive lessOne, bitWeight]
  | true =>
      simp only [Bool.true_and]
      rw [connected_retention_bool_fiber network p positive lessOne retention]
      simp

theorem actual_child_retention_observable
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (_outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (p : ℝ) (positive : 0 < inner.reliability p) (lessOne : inner.reliability p < 1)
    (coarse : Configuration outerEdges) (retention : Configuration innerEdges → Bool)
    (response : Configuration outerEdges → ℝ) :
    (∑ cells : Fin outerEdges → Configuration innerEdges,
      (∏ edge, inner.conditionalCellWeight p (coarse edge) (cells edge)) *
        response (fun edge => coarse edge && retention (cells edge))) =
      ∑ retain : Configuration outerEdges,
        bernoulliWeight (connectedRetentionProbability inner p retention) retain *
          response (fun edge => coarse edge && retain edge) := by
  classical
  let pushed : Fin outerEdges → Bool → ℝ := fun edge output =>
    ∑ retain : Bool, if (coarse edge && retain) = output then
      bitWeight (connectedRetentionProbability inner p retention) retain else 0
  have fromChildren := finite_product_state_selection_observable
    (fun edge configuration => inner.conditionalCellWeight p (coarse edge) configuration)
    (fun edge configuration => coarse edge && retention configuration) pushed
    (fun edge output => (conditional_retention_state_fiber inner p positive lessOne retention
      (coarse edge) output).symm) response
  have fromBits := finite_product_state_selection_observable
    (fun (_ : Fin outerEdges) retain => bitWeight (connectedRetentionProbability inner p retention) retain)
    (fun edge retain => coarse edge && retain) pushed (fun _ _ => rfl) response
  exact fromChildren.symm.trans fromBits

def configurationPairEquiv (edges : ℕ) :
    (Configuration edges × Configuration edges) ≃ (Fin edges → Bool × Bool) where
  toFun pair edge := (pair.1 edge, pair.2 edge)
  invFun sample := (fun edge => (sample edge).1, fun edge => (sample edge).2)
  left_inv pair := by cases pair; rfl
  right_inv sample := by funext edge; exact Prod.eta (sample edge)

theorem conditional_independent_retention_crossing {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ) (fixedPoint : network.reliability p = p)
    (retain : ℝ) :
    (∑ coarse : Configuration edges, network.conditionalCellWeight p true coarse *
      ∑ retained : Configuration edges, bernoulliWeight retain retained *
        (if network.crosses (fun edge => coarse edge && retained edge) then 1 else 0)) =
      network.reliability (p * retain) / p := by
  classical
  calc
    _ = (∑ sample : Fin edges → Bool × Bool,
        if network.crosses (originalConfiguration sample) then
          pairedConfigurationWeight p retain sample *
            (if network.crosses (thinnedConfiguration sample) then 1 else 0)
        else 0) / p := by
      rw [← (configurationPairEquiv edges).sum_comp, Fintype.sum_prod_type, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro coarse _
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro retained _
      simp only [pairedConfigurationWeight_eq_product]
      change network.conditionalCellWeight p true coarse *
          (bernoulliWeight retain retained *
            (if network.crosses (fun edge => coarse edge && retained edge) then 1 else 0)) =
        (if network.crosses coarse then
          bernoulliWeight p coarse * bernoulliWeight retain retained *
            (if network.crosses (fun edge => coarse edge && retained edge) then 1 else 0)
        else 0) / p
      cases crossing : network.crosses coarse <;>
        simp [FiniteNetwork.conditionalCellWeight, fixedPoint, crossing, div_mul_eq_mul_div, ite_div]
    _ = _ := conditional_thinning_at_fixed_point network fixedPoint retain

/-- Exact thinning probability for the true root-conditioned product of
actual child configuration laws. The retention predicate is arbitrary. -/
theorem actual_conditional_child_thinning
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (p : ℝ) (positive : 0 < inner.reliability p) (lessOne : inner.reliability p < 1)
    (fixedPoint : outer.reliability p = p) (retention : Configuration innerEdges → Bool) :
    (∑ coarse : Configuration outerEdges, outer.conditionalCellWeight p true coarse *
      ∑ cells : Fin outerEdges → Configuration innerEdges,
        (∏ edge, inner.conditionalCellWeight p (coarse edge) (cells edge)) *
          (if outer.crosses (fun edge => coarse edge && retention (cells edge)) then 1 else 0)) =
      outer.reliability (p * connectedRetentionProbability inner p retention) / p := by
  calc
    _ = ∑ coarse : Configuration outerEdges, outer.conditionalCellWeight p true coarse *
        ∑ retain : Configuration outerEdges,
          bernoulliWeight (connectedRetentionProbability inner p retention) retain *
            (if outer.crosses (fun edge => coarse edge && retain edge) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro coarse _
      congr 1
      exact actual_child_retention_observable outer inner p positive lessOne coarse retention
        (fun configuration => if outer.crosses configuration then 1 else 0)
    _ = _ := conditional_independent_retention_crossing outer p fixedPoint _

theorem actual_generation_child_thinning (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    (retention : Configuration (rule.generation depth).edges → Bool) :
    (∑ configuration : Configuration (rule.generation (depth + 1)).edges,
      (rule.generation (depth + 1)).network.conditionalCellWeight p true configuration *
        (if rule.network.crosses (fun edge =>
          generationRootConfiguration rule depth configuration edge &&
            retention (generationTopCells rule depth configuration edge)) then 1 else 0)) =
      rule.network.reliability
        (p * connectedRetentionProbability (rule.generation depth).network p retention) / p := by
  rw [generation_root_children_observable rule p positive lessOne fixedPoint true depth
    (fun coarse cells => if rule.network.crosses (fun edge => coarse edge && retention (cells edge)) then 1 else 0)]
  exact actual_conditional_child_thinning rule.network (rule.generation depth).network p
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint]) fixedPoint retention

theorem actual_history_child_thinning (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    (retention : Configuration (rule.generation depth).edges → Bool) :
    (∑ history : rule.ConfigurationHistory (depth + 1),
      Rule.ConfigurationHistory.recursiveWeight rule p true (depth + 1) history *
        (if rule.network.crosses (fun edge =>
          historyRootConfiguration rule depth history edge &&
            retention (historyChildConfiguration rule depth history edge)) then 1 else 0)) =
      rule.network.reliability
        (p * connectedRetentionProbability (rule.generation depth).network p retention) / p := by
  have law := history_root_children_observable rule p positive lessOne fixedPoint true depth
    (fun coarse children => if rule.network.crosses (fun edge => coarse edge &&
      retention (Rule.ConfigurationHistory.latest rule depth (children edge))) then 1 else 0)
  simp only [historyChildHistory_latest, Rule.ConfigurationHistory.latest_ofFine] at law
  rw [law]
  exact actual_conditional_child_thinning rule.network (rule.generation depth).network p
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint]) fixedPoint retention

end IGSIII.Chemical.Substitution

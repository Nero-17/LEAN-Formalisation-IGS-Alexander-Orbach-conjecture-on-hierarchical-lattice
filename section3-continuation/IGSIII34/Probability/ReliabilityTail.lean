import IGSIII34.Probability.ScalarSmallBall
import Universality.Percolation.RenormalisationLimits
import Universality.Percolation.BernoulliMonotonicity

/-! The actual normalized reliability map used by the chemical small-ball proof.
The graph hypotheses are explicit, and all its analytic properties below follow
from the vendored finite-network theorems rather than from a small-ball conclusion. -/

set_option autoImplicit false

namespace IGSIII34.Probability

open Universality Filter
open scoped Topology

noncomputable section

variable {vertices edges : ℕ}

def thinningMap (network : FiniteNetwork vertices edges) (critical value : ℝ) : ℝ :=
  network.reliability (critical * value) / critical

theorem thinningMap_zero (network : FiniteNetwork vertices edges) (critical : ℝ) :
    thinningMap network critical 0 = 0 := by
  simp [thinningMap, network.reliability_zero]

theorem thinningMap_nonnegative (network : FiniteNetwork vertices edges)
    {critical value : ℝ} (criticalPositive : 0 < critical)
    (criticalBelowOne : critical < 1) (valueNonnegative : 0 ≤ value)
    (valueAtMostOne : value ≤ 1) : 0 ≤ thinningMap network critical value := by
  apply div_nonneg _ criticalPositive.le
  exact network.reliability_nonneg (mul_nonneg criticalPositive.le valueNonnegative)
    ((mul_le_mul_of_nonneg_left valueAtMostOne criticalPositive.le).trans
      (by simpa using criticalBelowOne.le))

theorem thinningMap_strict (network : FiniteNetwork vertices edges)
    {critical value : ℝ} (criticalPositive : 0 < critical)
    (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (valuePositive : 0 < value) (valueBelowOne : value < 1) :
    thinningMap network critical value < value := by
  apply (div_lt_iff₀ criticalPositive).mpr
  simpa only [mul_comm value critical] using
    network.reliability_lt_parameter_below_fixed critical (critical * value)
      criticalPositive criticalBelowOne fixedPoint (mul_pos criticalPositive valuePositive)
      (by simpa using mul_lt_mul_of_pos_left valueBelowOne criticalPositive) scale

theorem thinningMap_monotoneOn (network : FiniteNetwork vertices edges)
    {critical : ℝ} (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1) :
    MonotoneOn (thinningMap network critical) (Set.Icc 0 1) := by
  intro first firstWithin second secondWithin ordered
  apply div_le_div_of_nonneg_right _ criticalPositive.le
  apply network.reliability_monotoneOn
  · exact ⟨mul_nonneg criticalPositive.le firstWithin.1,
      (mul_le_mul_of_nonneg_left firstWithin.2 criticalPositive.le).trans
        (by simpa using criticalBelowOne.le)⟩
  · exact ⟨mul_nonneg criticalPositive.le secondWithin.1,
      (mul_le_mul_of_nonneg_left secondWithin.2 criticalPositive.le).trans
        (by simpa using criticalBelowOne.le)⟩
  · exact mul_le_mul_of_nonneg_left ordered criticalPositive.le

theorem thinningMap_iterate (network : FiniteNetwork vertices edges)
    {critical : ℝ} (criticalNonzero : critical ≠ 0) (start : ℝ) (depth : ℕ) :
    (thinningMap network critical)^[depth] start =
      network.reliability^[depth] (critical * start) / critical := by
  induction depth with
  | zero => simp [criticalNonzero]
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', inductionHypothesis]
    unfold thinningMap
    congr 2
    field_simp

theorem thinningMap_weighted_iterate_summable (network : FiniteNetwork vertices edges)
    {critical start growth : ℝ} (criticalPositive : 0 < critical)
    (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (growthPositive : 0 < growth) :
    Summable (fun depth : ℕ => growth ^ depth * (thinningMap network critical)^[depth] start) := by
  have derivative : HasDerivAt network.reliability 0 0 := by
    have derivative := (network.hasDerivAt_reliability 0).differentiableAt.hasDerivAt
    rwa [network.derivative_zero_zero scale] at derivative
  have summability := Universality.summable_weighted_iterate_sub_of_derivative_zero
    network.reliability (critical * start) 0 growth growthPositive network.reliability_zero
    derivative (network.iterate_reliability_tendsto_zero critical (critical * start)
      criticalPositive criticalBelowOne fixedPoint
      (mul_nonneg criticalPositive.le startNonnegative)
      (by simpa using mul_lt_mul_of_pos_left startBelowOne criticalPositive) scale)
  have divided := summability.div_const critical
  apply divided.congr
  intro depth
  rw [thinningMap_iterate network criticalPositive.ne']
  simp only [sub_zero, mul_div_assoc]

end
end IGSIII34.Probability

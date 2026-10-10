import IGSIII.Chemical.SmallBall.Thinning
import Universality.Probability.FiniteWeightMeasure

/-! The finite thinning calculation as a genuine normalized probability law. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork
open scoped BigOperators

noncomputable section

variable {vertices edges : ℕ}

def conditionedPairedWeight (network : FiniteNetwork vertices edges)
    (critical retain : ℝ) (sample : Fin edges → Bool × Bool) : ℝ :=
  if network.crosses (originalConfiguration sample) then
    pairedConfigurationWeight critical retain sample / critical else 0

theorem conditionedPairedWeight_nonnegative (network : FiniteNetwork vertices edges)
    {critical retain : ℝ} (criticalPositive : 0 < critical) (criticalAtMostOne : critical ≤ 1)
    (retainNonnegative : 0 ≤ retain) (retainAtMostOne : retain ≤ 1)
    (sample : Fin edges → Bool × Bool) :
    0 ≤ conditionedPairedWeight network critical retain sample := by
  unfold conditionedPairedWeight
  split
  · exact div_nonneg (pairedConfigurationWeight_nonnegative criticalPositive.le
      criticalAtMostOne retainNonnegative retainAtMostOne sample) criticalPositive.le
  · exact le_rfl

theorem sum_conditionedPairedWeight (network : FiniteNetwork vertices edges)
    {critical : ℝ} (criticalNonzero : critical ≠ 0)
    (fixedPoint : network.reliability critical = critical) (retain : ℝ) :
    ∑ sample : Fin edges → Bool × Bool,
      conditionedPairedWeight network critical retain sample = 1 := by
  have equality := original_crossing_weight network critical retain
  have normalized := congrArg (fun value : ℝ => value / critical) equality
  rw [fixedPoint, div_self criticalNonzero] at normalized
  simpa only [conditionedPairedWeight, Finset.sum_div, mul_ite, mul_one, mul_zero,
    ite_div, zero_div] using normalized

/-- Independent original and retention bits, conditioned only on original crossing. -/
def conditionedPairedPMF (network : FiniteNetwork vertices edges)
    {critical retain : ℝ} (criticalPositive : 0 < critical) (criticalAtMostOne : critical ≤ 1)
    (fixedPoint : network.reliability critical = critical)
    (retainNonnegative : 0 ≤ retain) (retainAtMostOne : retain ≤ 1) :
    PMF (Fin edges → Bool × Bool) :=
  finiteWeightPMF (conditionedPairedWeight network critical retain)
    (conditionedPairedWeight_nonnegative network criticalPositive criticalAtMostOne
      retainNonnegative retainAtMostOne)
    (sum_conditionedPairedWeight network criticalPositive.ne' fixedPoint retain)

theorem conditioned_crossing_probability (network : FiniteNetwork vertices edges)
    {critical : ℝ} (fixedPoint : network.reliability critical = critical) (retain : ℝ) :
    (∑ sample : Fin edges → Bool × Bool,
      conditionedPairedWeight network critical retain sample *
        (if network.crosses (thinnedConfiguration sample) then 1 else 0)) =
      network.reliability (critical * retain) / critical := by
  have equality := conditional_thinning_at_fixed_point network fixedPoint retain
  rw [Finset.sum_div] at equality
  convert equality using 1
  apply Finset.sum_congr rfl
  intro sample _
  unfold conditionedPairedWeight
  split <;> simp [ite_div]

end
end IGSIII.Chemical.SmallBall

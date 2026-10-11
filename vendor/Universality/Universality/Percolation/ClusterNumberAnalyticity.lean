import Universality.Analysis.PolynomialDiscountedAnalytic
import Universality.Percolation.ClusterNumberCriticalDerivative

namespace Universality.FiniteNetwork
noncomputable section
open Polynomial

/-- The polynomial orbit series on all real parameters. On [0,1] it agrees
exactly with the actual volume-limit density; near either endpoint it supplies
the analytic extension, avoiding an artificial zero-extension discontinuity. -/
def clusterNumberAnalyticExtension {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) : ℝ :=
  ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) *
    discountedIteration (R.reliabilityPolynomial.map (Rat.castHom ℝ)).eval
      (R.internalClusterPolynomial.map (Int.castRingHom ℝ)).eval (1 / (edges : ℝ)) p

theorem clusterNumberAnalyticExtension_eq {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : Set.Icc (0 : ℝ) 1) :
    R.clusterNumberAnalyticExtension p.val = R.clusterNumberSeries p := by
  have hcrossing : (R.reliabilityPolynomial.map (Rat.castHom ℝ)).eval = R.reliability := by
    funext x
    rw [Polynomial.eval_map, R.reliabilityPolynomial_eval]
  have hforcing (x : ℝ) : (R.internalClusterPolynomial.map (Int.castRingHom ℝ)).eval x =
      R.expectedInternalClusterNumber x := by
    rw [Polynomial.eval_map, R.internalClusterPolynomial_eval]
  simp only [clusterNumberAnalyticExtension, clusterNumberSeries, discountedIteration,
    hcrossing, hforcing, R.unitReliability_iterate_val]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter
open scoped Topology

/-- Actual off-critical analyticity, including an analytic extension across
both endpoint parameters. No regularity of the physical density is assumed. -/
theorem Classical.cluster_number_analyticAt_offcritical {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hne : p ≠ critical) :
    AnalyticAt ℝ rule.network.clusterNumberAnalyticExtension p := by
  let crossing : Polynomial ℝ := rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)
  let forcing : Polynomial ℝ := rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)
  have hcrossing : crossing.eval = rule.network.reliability := by
    funext x
    simp only [crossing, Polynomial.eval_map, reliabilityPolynomial_eval]
  have hderivative (x : ℝ) : crossing.derivative.eval x = deriv rule.network.reliability x := by
    dsimp [crossing]
    rw [Polynomial.derivative_map, Polynomial.eval_map,
      (rule.network.hasDerivAt_reliability x).deriv]
  have hmass : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hdiscount : |1 / (rule.edges : ℝ)| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr (zero_lt_one.trans hmass))]
    exact (div_lt_one (zero_lt_one.trans hmass)).mpr hmass
  change AnalyticAt ℝ (fun x =>
    ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
      discountedIteration crossing.eval forcing.eval (1 / (rule.edges : ℝ)) x) p
  apply analyticAt_const.mul
  rcases lt_or_gt_of_ne hne with hside | hside
  · apply polynomialDiscountedIteration_analyticAt_of_attracted crossing forcing
      (1 / (rule.edges : ℝ)) p 0 hdiscount
    · rw [congrFun hcrossing 0]
      exact rule.network.reliability_zero
    · rw [hderivative]
      exact rule.network.derivative_zero_zero h.scale
    · rw [hcrossing]
      exact rule.network.iterate_reliability_tendsto_zero critical p hc hc' hfixed hp hside h.scale
  · apply polynomialDiscountedIteration_analyticAt_of_attracted crossing forcing
      (1 / (rule.edges : ℝ)) p 1 hdiscount
    · rw [congrFun hcrossing 1]
      exact rule.network.reliability_one (h.connected _)
    · rw [hderivative]
      exact rule.network.derivative_one_zero h.cut
    · rw [hcrossing]
      exact rule.network.iterate_reliability_tendsto_one critical p hc hc' hfixed hside hp' h.scale

theorem Classical.cluster_number_densityExtension_analyticAt_offcritical {rule : Rule}
    (h : rule.Classical) (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) :
    AnalyticAt ℝ rule.network.clusterNumberDensityExtension p := by
  apply (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.le hp'.le hne).congr
  filter_upwards [Ioo_mem_nhds hp hp'] with q hq
  have hclosed : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
  rw [rule.network.clusterNumberAnalyticExtension_eq ⟨q, hclosed⟩,
    rule.network.clusterNumberDensityExtension_eq ⟨q, hclosed⟩]

end
end Universality.Rule

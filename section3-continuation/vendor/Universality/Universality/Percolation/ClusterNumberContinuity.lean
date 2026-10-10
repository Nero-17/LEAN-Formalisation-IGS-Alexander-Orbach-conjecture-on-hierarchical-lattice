import Universality.Percolation.ClusterNumberPolynomial
import Universality.Percolation.ClusterNumberSeries
import Universality.Analysis.ContinuousDiscountedIteration
import Mathlib.Topology.Algebra.Polynomial

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem continuous_expectedInternalClusterNumber : Continuous R.expectedInternalClusterNumber := by
  have h : R.expectedInternalClusterNumber =
      fun p => (R.internalClusterPolynomial.map (Int.castRingHom ℝ)).eval p := by
    funext p
    rw [Polynomial.eval_map, R.internalClusterPolynomial_eval]
  rw [h]
  exact Polynomial.continuous _

theorem continuous_unitReliability : Continuous R.unitReliability := by
  apply Continuous.subtype_mk
  have h : R.reliability = fun p => (R.reliabilityPolynomial.map (Rat.castHom ℝ)).eval p := by
    funext p
    rw [Polynomial.eval_map, R.reliabilityPolynomial_eval]
  change Continuous (fun p : Set.Icc (0 : ℝ) 1 => R.reliability p.val)
  rw [h]
  exact (Polynomial.continuous _).comp continuous_subtype_val

theorem continuous_clusterNumberSeries (hedges : 1 < edges) : Continuous R.clusterNumberSeries := by
  have hm : (1 : ℝ) < edges := by exact_mod_cast hedges
  apply continuous_const.mul
  apply continuous_discountedIteration R.unitReliability
    (fun p => R.expectedInternalClusterNumber p.val) (1 / (edges : ℝ)) (vertices : ℝ)
    R.continuous_unitReliability
    (R.continuous_expectedInternalClusterNumber.comp continuous_subtype_val)
    (one_div_nonneg.mpr (lt_trans zero_lt_one hm).le)
    ((div_lt_one (lt_trans zero_lt_one hm)).mpr hm)
  intro p
  rw [abs_of_nonneg (R.expectedInternalClusterNumber_bounds p.property.1 p.property.2).1]
  exact (R.expectedInternalClusterNumber_bounds p.property.1 p.property.2).2

end
end Universality.FiniteNetwork

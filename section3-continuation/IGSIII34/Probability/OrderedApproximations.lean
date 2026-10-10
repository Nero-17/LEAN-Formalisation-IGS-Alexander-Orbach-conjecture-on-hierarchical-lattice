import IGSIII.Probability.OmegaOrbit
import Mathlib.MeasureTheory.Function.LpOrder

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology ENNReal
variable {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)

theorem lp_positive_difference_norm_le
    (first second firstApproximation secondApproximation : Lp ℝ 2 measure)
    (scalar : ℝ) (comparison : firstApproximation ≤ scalar • secondApproximation) :
    ‖(first-scalar • second) ⊔ 0‖ ≤
      ‖first-firstApproximation‖ + |scalar| *‖second-secondApproximation‖ := by
  have zero : (firstApproximation-scalar • secondApproximation) ⊔ 0 = 0 :=
    sup_eq_right.mpr (sub_nonpos.mpr comparison)
  have bound := norm_sup_sub_sup_le_norm
    (first-scalar • second) (firstApproximation-scalar • secondApproximation) 0
  rw [zero, sub_zero] at bound
  refine bound.trans ?_
  have equality : first-scalar • second-(firstApproximation-scalar • secondApproximation) =
      (first-firstApproximation)-scalar • (second-secondApproximation) := by
    simp only [smul_sub]
    abel
  rw [equality]
  simpa only [norm_smul, Real.norm_eq_abs] using
    norm_sub_le (first-firstApproximation) (scalar • (second-secondApproximation))

theorem orbitClusterSet_pairwise_le_of_ordered_approximations
    (sequence : ℕ → Lp ℝ 2 measure) (approximation : ℕ → ℕ → Lp ℝ 2 measure)
    (error : ℕ → ℝ) (errorTendstoZero : Tendsto error atTop (𝓝 0)) (scalar : ℝ)
    (approximates : ∀ coarse depth, coarse+2 ≤ depth → ‖sequence depth-approximation coarse depth‖ ≤ error coarse)
    (ordered : ∀ coarse first second, coarse+2 ≤ first → coarse+2 ≤ second →
      approximation coarse first ≤ scalar • approximation coarse second)
    (first second : Lp ℝ 2 measure)
    (firstMember : first ∈ IGSIII.Probability.orbitClusterSet sequence)
    (secondMember : second ∈ IGSIII.Probability.orbitClusterSet sequence) :
    first ≤ scalar • second := by
  have finiteBound (coarse firstDepth secondDepth : ℕ)
      (firstLarge : coarse+2 ≤ firstDepth) (secondLarge : coarse+2 ≤ secondDepth) :
      ‖(sequence firstDepth-scalar • sequence secondDepth) ⊔ 0‖ ≤
        error coarse*(1+|scalar|) := by
    refine (lp_positive_difference_norm_le measure _ _ _ _ scalar
      (ordered coarse firstDepth secondDepth firstLarge secondLarge)).trans ?_
    have bound := add_le_add (approximates coarse firstDepth firstLarge)
      (mul_le_mul_of_nonneg_left (approximates coarse secondDepth secondLarge) (abs_nonneg scalar))
    nlinarith
  have bound (coarse : ℕ) : ‖(first-scalar • second) ⊔ 0‖ ≤ error coarse*(1+|scalar|) := by
    have firstBound (secondDepth : ℕ) (secondLarge : coarse+2 ≤ secondDepth) :
        ‖(first-scalar • sequence secondDepth) ⊔ 0‖ ≤ error coarse*(1+|scalar|) := by
      have continuous : Continuous (fun point : Lp ℝ 2 measure => ‖(point-scalar • sequence secondDepth) ⊔ 0‖) :=
        ((continuous_id.sub continuous_const).sup continuous_const).norm
      apply (isClosed_Iic : IsClosed (Set.Iic (error coarse*(1+|scalar|)))).mem_of_mapClusterPt
        (firstMember.continuousAt_comp continuous.continuousAt)
      filter_upwards [eventually_ge_atTop (coarse+2)] with depth large
      exact finiteBound coarse depth secondDepth large secondLarge
    have continuous : Continuous (fun point : Lp ℝ 2 measure => ‖(first-scalar • point) ⊔ 0‖) :=
      by
        have scaled : Continuous (fun point : Lp ℝ 2 measure => scalar • point) := continuous_const_smul scalar
        exact ((continuous_const.sub scaled).sup continuous_const).norm
    apply (isClosed_Iic : IsClosed (Set.Iic (error coarse*(1+|scalar|)))).mem_of_mapClusterPt
      (secondMember.continuousAt_comp continuous.continuousAt)
    filter_upwards [eventually_ge_atTop (coarse+2)] with depth large
    exact firstBound depth large
  have zeroNorm : ‖(first-scalar • second) ⊔ 0‖ = 0 := le_antisymm
    (by simpa only [zero_mul] using ge_of_tendsto' (errorTendstoZero.mul_const (1+|scalar|)) bound)
    (norm_nonneg _)
  have zero := norm_eq_zero.mp zeroNorm
  exact sub_nonpos.mp ((le_sup_left : first-scalar • second ≤ (first-scalar • second) ⊔ 0).trans_eq zero)

end
end IGSIII34.Probability

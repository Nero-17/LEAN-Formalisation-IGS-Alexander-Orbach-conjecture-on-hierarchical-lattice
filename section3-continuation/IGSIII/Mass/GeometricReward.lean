import IGSIII.Mass.BorelCantelli
import Universality.Probability.FourthMomentConvergence
import Universality.Probability.L2LimitOperations
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

namespace IGSIII.Mass

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {probability : Measure Ω}

/-- A birth-reward error with a geometrically bounded second moment has a
negligible accumulated error almost surely at the growth scale. The estimate
does not assume independence or cancellation between generations. -/
theorem ae_normalized_sum_zero_of_second_moment_bound
    (innovation : ℕ → Ω → ℝ) (square_integrable : ∀ n, MemLp (innovation n) 2 probability)
    (bound radius : ℝ) (bound_nonnegative : 0 ≤ bound) (radius_gt_one : 1 < radius)
    (second_moment_bound : ∀ n, ∫ sample, innovation n sample ^ 2 ∂probability ≤
      bound * radius ^ n) :
    ∀ᵐ sample ∂probability,
      Tendsto (fun n => (∑ k ∈ Finset.range n, innovation k sample) / radius ^ n)
        atTop (𝓝 0) := by
  have radius_positive : 0 < radius := zero_lt_one.trans radius_gt_one
  have sqrt_gt_one : 1 < Real.sqrt radius := (Real.lt_sqrt (by norm_num)).mpr (by simpa)
  have sqrt_lt_radius : Real.sqrt radius < radius := by
    nlinarith [Real.sq_sqrt radius_positive.le, Real.sqrt_nonneg radius]
  have single_bound (n : ℕ) : eLpNorm (innovation n) 2 probability ≤
      ENNReal.ofReal (Real.sqrt bound * Real.sqrt radius ^ n) := by
    apply Universality.eLpNorm_two_le_of_integral_sq_le (square_integrable n)
      (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) n))
    convert second_moment_bound n using 1
    rw [mul_pow, Real.sq_sqrt bound_nonnegative, ← pow_mul, Nat.mul_comm n 2,
      pow_mul, Real.sq_sqrt radius_positive.le]
  have sum_bound (n : ℕ) : eLpNorm (∑ k ∈ Finset.range n, innovation k) 2 probability ≤
      ENNReal.ofReal (Real.sqrt bound * (Real.sqrt radius ^ n / (Real.sqrt radius - 1))) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, eLpNorm (innovation k) 2 probability :=
        eLpNorm_sum_le (fun k _ => (square_integrable k).aestronglyMeasurable) (by norm_num)
      _ ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (Real.sqrt bound * Real.sqrt radius ^ k) :=
        Finset.sum_le_sum (fun k _ => single_bound k)
      _ = ENNReal.ofReal (Real.sqrt bound * ∑ k ∈ Finset.range n, Real.sqrt radius ^ k) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
          mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) k)), Finset.mul_sum]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply (le_div_iff₀ (sub_pos.mpr sqrt_gt_one)).mpr
        rw [geom_sum_mul]
        linarith
  apply ae_tendsto_zero_of_geometric_L2
    (fun n sample => (∑ k ∈ Finset.range n, innovation k sample) / radius ^ n)
    (fun n => (Universality.memLp_div_const_real
      (memLp_finsetSum _ (fun k _ => square_integrable k)) _).aestronglyMeasurable)
    (Real.sqrt bound / (Real.sqrt radius - 1)) (Real.sqrt radius / radius)
    (div_nonneg (Real.sqrt_nonneg _) (sub_pos.mpr sqrt_gt_one).le)
    (div_nonneg (Real.sqrt_nonneg _) radius_positive.le)
    ((div_lt_one radius_positive).mpr sqrt_lt_radius)
  intro n
  have normalized_eq : (fun sample => (∑ k ∈ Finset.range n, innovation k sample) / radius ^ n) =
      (radius ^ n)⁻¹ • (∑ k ∈ Finset.range n, innovation k) := by
    funext sample
    simp [div_eq_mul_inv, mul_comm]
  rw [normalized_eq, eLpNorm_const_smul,
    Real.enorm_of_nonneg (inv_nonneg.mpr (pow_nonneg radius_positive.le n))]
  apply (mul_le_mul_right (sum_bound n) _).trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg radius_positive.le n))]
  congr 1
  rw [div_pow]
  ring

end IGSIII.Mass

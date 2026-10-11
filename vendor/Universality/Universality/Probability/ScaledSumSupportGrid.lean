import Universality.Probability.L2Characteristic
import Mathlib.Algebra.Order.Floor.Semiring

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem scaled_sum_support_zero (support : Set ℝ) (degree : ℕ) (radius : ℝ)
    (hclosed : IsClosed support) (hnonempty : support.Nonempty)
    (hradius : 0 < radius) (hdegree : (degree : ℝ) < radius)
    (hsum : ∀ value : Fin degree → ℝ,
      (∀ i, value i ∈ support) → (∑ i, value i) / radius ∈ support) :
    0 ∈ support := by
  obtain ⟨point, hpoint⟩ := hnonempty
  have hmem (n : ℕ) : ((degree : ℝ) / radius) ^ n * point ∈ support := by
    induction n with
    | zero => simpa using hpoint
    | succ n ih =>
      have h := hsum (fun _ => ((degree : ℝ) / radius) ^ n * point) (fun _ => ih)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
      convert h using 1 <;> rw [pow_succ] <;> ring
  have hconvergence : Tendsto (fun n : ℕ => ((degree : ℝ) / radius) ^ n * point) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (Nat.cast_nonneg _) hradius.le)
        ((div_lt_one hradius).mpr hdegree)).mul_const point
  exact hclosed.mem_of_tendsto hconvergence (Eventually.of_forall hmem)

theorem exists_bounded_fin_sum (slots capacity total : ℕ) (htotal : total ≤ slots * capacity) :
    ∃ value : Fin slots → ℕ, (∀ i, value i ≤ capacity) ∧ ∑ i, value i = total := by
  induction slots generalizing total with
  | zero =>
    have : total = 0 := by omega
    subst total
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ slots ih =>
    have hremainder : total - min total capacity ≤ slots * capacity := by
      rw [Nat.succ_mul] at htotal
      omega
    obtain ⟨value, hvalue, hsum⟩ := ih _ hremainder
    refine ⟨Fin.cons (min total capacity) value, ?_, ?_⟩
    · intro i
      refine Fin.cases (Nat.min_le_right _ _) (fun j => hvalue j) i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hsum]
      omega

/-- Closure under one d-ary scaled sum implies every finite grid obtained
by independently selecting zero or one fixed support value at depth k. -/
theorem scaled_sum_support_grid (support : Set ℝ) (degree : ℕ) (radius : ℝ)
    (hradius : 0 < radius) (hzero : 0 ∈ support)
    (hsum : ∀ value : Fin degree → ℝ,
      (∀ i, value i ∈ support) → (∑ i, value i) / radius ∈ support)
    (point : ℝ) (hpoint : point ∈ support) (depth count : ℕ)
    (hcount : count ≤ degree ^ depth) :
    (count : ℝ) * point / radius ^ depth ∈ support := by
  induction depth generalizing count with
  | zero =>
    simp only [pow_zero] at hcount ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcount with rfl | rfl
    · simpa using hzero
    · simpa using hpoint
  | succ depth ih =>
    have hdecompose : count ≤ degree * degree ^ depth := by
      simpa only [pow_succ, Nat.mul_comm] using hcount
    obtain ⟨value, hvalue, hvalueSum⟩ := exists_bounded_fin_sum degree (degree ^ depth) count hdecompose
    have hmem := hsum (fun i => (value i : ℝ) * point / radius ^ depth)
      (fun i => ih (value i) (hvalue i))
    have heq : (∑ i : Fin degree, (value i : ℝ) * point / radius ^ depth) / radius =
        (count : ℝ) * point / radius ^ (depth + 1) := by
      rw [← Finset.sum_div, ← Finset.sum_mul, ← Nat.cast_sum, hvalueSum, pow_succ, div_div]
    rwa [heq] at hmem

end
end Universality

import Universality.Analysis.GeometricWindowComparison

namespace Universality
noncomputable section

/-- A pre-exit geometric bound and a whole-tail bound imply the same
geometric upper estimate for the entire nonnegative series. -/
theorem stopped_series_geometric_upper (sequence : ℕ → ℝ) (ratio upper tail : ℝ) (depth : ℕ)
    (hratio : 0 < ratio) (hupper : 0 ≤ upper) (htail : 0 ≤ tail) (hdepth : 1 ≤ depth)
    (hnonneg : ∀ n, 0 ≤ sequence n)
    (hpre : ∀ n, n < depth → sequence n ≤ upper * ratio ^ n)
    (hsummable : Summable (fun n : ℕ => sequence (depth + n)))
    (hpost : (∑' n : ℕ, sequence (depth + n)) ≤ tail * ratio ^ depth) :
    Summable sequence ∧ (∑' n : ℕ, sequence n) ≤
      (upper + tail * ratio) * ∑ n ∈ Finset.range depth, ratio ^ n := by
  have hs : Summable sequence := (summable_nat_add_iff depth).mp
    (by simpa only [Nat.add_comm depth] using hsummable)
  have hfinite : (∑ n ∈ Finset.range depth, sequence n) ≤ upper *
      ∑ n ∈ Finset.range depth, ratio ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n hn => hpre n (Finset.mem_range.mp hn))
  have hlast : ratio ^ (depth - 1) ≤ ∑ n ∈ Finset.range depth, ratio ^ n :=
    Finset.single_le_sum (fun n _ => (pow_pos hratio n).le) (Finset.mem_range.mpr (by omega))
  have hpower : ratio ^ depth ≤ ratio * ∑ n ∈ Finset.range depth, ratio ^ n := by
    have hh := mul_le_mul_of_nonneg_left hlast hratio.le
    rw [← pow_succ', show depth - 1 + 1 = depth by omega] at hh
    exact hh
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add depth]
  have hpost' : (∑' n : ℕ, sequence (n + depth)) ≤ tail * ratio ^ depth := by
    simpa only [Nat.add_comm depth] using hpost
  have hb := mul_le_mul_of_nonneg_left hpower htail
  nlinarith only [hfinite, hpost', hb]

/-- The fixed omitted prefix and the last two pre-exit generations do not
change the scale of the full moment series. -/
theorem stopped_series_geometric_lower (ratio : ℝ) (hratio : 0 < ratio) (start : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ sequence : ℕ → ℝ, ∀ lower : ℝ, 0 ≤ lower →
      (∀ n, 0 ≤ sequence n) → Summable sequence → ∀ depth : ℕ, start + 3 ≤ depth →
      (∀ n, start ≤ n → n + 2 < depth → lower * ratio ^ n ≤ sequence n) →
      (constant * lower) * (∑ n ∈ Finset.range depth, ratio ^ n) ≤ ∑' n : ℕ, sequence n := by
  obtain ⟨constant, hconstant, hb⟩ := geometric_window_lower ratio hratio start 2
  refine ⟨constant, hconstant, ?_⟩
  intro sequence lower hlower hnonneg hs depth hdepth hpre
  have hlength : 1 ≤ depth - start - 2 := by omega
  have hwindow := hb (depth - start - 2) hlength
  rw [show depth - start - 2 + start + 2 = depth by omega] at hwindow
  have hpreSum : lower * (∑ n ∈ Finset.range (depth - start - 2), ratio ^ (start + n)) ≤
      ∑ n ∈ Finset.range (depth - start - 2), sequence (start + n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    exact hpre (start + n) (by omega) (by have := Finset.mem_range.mp hn; omega)
  let embedding : ℕ ↪ ℕ := ⟨fun n => start + n, fun _ _ hh => Nat.add_left_cancel hh⟩
  have hpartial := hs.sum_le_tsum ((Finset.range (depth - start - 2)).map embedding)
    (fun n _ => hnonneg n)
  simp only [Finset.sum_map, embedding, Function.Embedding.coeFn_mk] at hpartial
  have hh := mul_le_mul_of_nonneg_left hwindow hlower
  calc
    _ = lower * (constant * ∑ n ∈ Finset.range depth, ratio ^ n) := by ring
    _ ≤ _ := hh
    _ ≤ _ := hpreSum
    _ ≤ _ := hpartial

end
end Universality

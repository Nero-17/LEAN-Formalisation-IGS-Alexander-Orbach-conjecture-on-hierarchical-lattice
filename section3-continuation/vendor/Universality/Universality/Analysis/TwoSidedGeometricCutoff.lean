import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section

/-- Bounds on the two sides of a size-selected generation. The part below
the generation is a reversed geometric sum, not an interchange of limits. -/
theorem two_sided_geometric_cutoff_sum (sequence : ℕ → ℝ)
    (scale firstRatio laterRatio constant : ℝ) (depth : ℕ)
    (hscale : 0 ≤ scale) (hfirst : 0 ≤ firstRatio) (hfirstOne : firstRatio < 1)
    (hlater : 0 ≤ laterRatio) (hlaterOne : laterRatio < 1) (hconstant : 0 ≤ constant)
    (hnonneg : ∀ n, 0 ≤ sequence n)
    (hpre : ∀ n, n ≤ depth → sequence n ≤ constant * scale ^ depth * firstRatio ^ (depth - n))
    (hpost : ∀ j, sequence (depth + 1 + j) ≤ constant * scale ^ depth * laterRatio ^ j) :
    Summable sequence ∧ (∑' n : ℕ, sequence n) ≤
      constant * scale ^ depth * ((1 - firstRatio)⁻¹ + (1 - laterRatio)⁻¹) := by
  have hcoefficient : 0 ≤ constant * scale ^ depth := mul_nonneg hconstant (pow_nonneg hscale _)
  have hlaterSum := (summable_geometric_of_lt_one hlater hlaterOne).mul_left (constant * scale ^ depth)
  have hpostSum : Summable (fun j => sequence (depth + 1 + j)) :=
    hlaterSum.of_nonneg_of_le (fun j => hnonneg _) hpost
  have hs : Summable sequence := (summable_nat_add_iff (depth + 1)).mp
    (by simpa only [Nat.add_comm (depth + 1)] using hpostSum)
  have hpreSum : (∑ n ∈ Finset.range (depth + 1), sequence n) ≤
      constant * scale ^ depth * (1 - firstRatio)⁻¹ := by
    calc
      _ ≤ ∑ n ∈ Finset.range (depth + 1), constant * scale ^ depth * firstRatio ^ (depth - n) :=
        Finset.sum_le_sum (fun n hn => hpre n (by have := Finset.mem_range.mp hn; omega))
      _ = constant * scale ^ depth * ∑ n ∈ Finset.range (depth + 1), firstRatio ^ n := by
        rw [← Finset.mul_sum]
        congr 1
        simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun n => firstRatio ^ n) (depth + 1)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hcoefficient
        have hh := (summable_geometric_of_lt_one hfirst hfirstOne).sum_le_tsum
          (Finset.range (depth + 1)) (fun n _ => pow_nonneg hfirst n)
        simpa only [tsum_geometric_of_lt_one hfirst hfirstOne] using hh
  have hpostBound : (∑' j : ℕ, sequence (j + (depth + 1))) ≤
      constant * scale ^ depth * (1 - laterRatio)⁻¹ := by
    have hh := hpostSum.tsum_le_tsum hpost hlaterSum
    simpa only [Nat.add_comm (depth + 1), tsum_mul_left,
      tsum_geometric_of_lt_one hlater hlaterOne] using hh
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add (depth + 1), mul_add]
  exact add_le_add hpreSum hpostBound

end
end Universality

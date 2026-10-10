import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality
noncomputable section

/-- Pointwise bounds before and after a stopping generation produce one
geometric majorant at every generation. -/
theorem stopped_sequence_geometric_domination (sequence : ℕ → ℝ)
    (firstGrowth laterGrowth upper tail : ℝ) (depth : ℕ)
    (hfirstGrowth : 0 ≤ firstGrowth) (hlaterGrowth : 0 ≤ laterGrowth)
    (hupper : 0 ≤ upper) (htail : 0 ≤ tail)
    (hpre : ∀ n, n < depth → sequence n ≤ upper * firstGrowth ^ n)
    (hpost : ∀ j, sequence (depth + j) ≤ tail * firstGrowth ^ depth * laterGrowth ^ j) :
    ∀ n, sequence n ≤ max upper tail * (max firstGrowth laterGrowth) ^ n := by
  intro n
  have hconstant : 0 ≤ max upper tail := hupper.trans (le_max_left _ _)
  have hfirst (j : ℕ) : firstGrowth ^ j ≤ (max firstGrowth laterGrowth) ^ j :=
    pow_le_pow_left₀ hfirstGrowth (le_max_left _ _) j
  have hlater (j : ℕ) : laterGrowth ^ j ≤ (max firstGrowth laterGrowth) ^ j :=
    pow_le_pow_left₀ hlaterGrowth (le_max_right _ _) j
  rcases lt_or_ge n depth with hbefore | hafter
  · exact (hpre n hbefore).trans
      (mul_le_mul (le_max_left _ _) (hfirst n) (pow_nonneg hfirstGrowth _) hconstant)
  · have hindex : depth + (n - depth) = n := by omega
    calc
      _ ≤ tail * firstGrowth ^ depth * laterGrowth ^ (n - depth) := by
        simpa only [hindex] using hpost (n - depth)
      _ ≤ (max upper tail * (max firstGrowth laterGrowth) ^ depth) *
          (max firstGrowth laterGrowth) ^ (n - depth) :=
        mul_le_mul (mul_le_mul (le_max_right _ _) (hfirst depth)
          (pow_nonneg hfirstGrowth _) hconstant) (hlater (n - depth))
          (pow_nonneg hlaterGrowth _) (mul_nonneg hconstant (pow_nonneg (hfirstGrowth.trans (le_max_left _ _)) _))
      _ = _ := by rw [mul_assoc, ← pow_add, hindex]

end
end Universality

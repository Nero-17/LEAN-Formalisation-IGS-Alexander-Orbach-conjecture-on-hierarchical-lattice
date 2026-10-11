import Universality.Algebra.GroupedWords
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Capacities of projected word groups

Every aggregate total below the total finite capacity has an actual integral
allocation.  The number of binary words with a prescribed zero count is the
binomial coefficient.  These are existence statements about leaf allocations;
the graph interpretation is kept separate.
-/

namespace Universality.Certificates

theorem exists_bounded_allocation (count capacity total : ℕ)
    (h : total ≤ count * capacity) :
    ∃ allocation : Fin count → ℕ,
      (∀ i, allocation i ≤ capacity) ∧ (∑ i, allocation i) = total := by
  induction count generalizing total with
  | zero =>
      have ht : total = 0 := by simpa using h
      subst total
      exact ⟨fun i => Fin.elim0 i, by simp, by simp⟩
  | succ count ih =>
      have hrest : total - min capacity total ≤ count * capacity := by
        rw [Nat.succ_mul] at h
        by_cases ht : capacity ≤ total
        · rw [min_eq_left ht]
          omega
        · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge ht))]
          simp
      obtain ⟨allocation, hcapacity, hsum⟩ := ih (total - min capacity total) hrest
      refine ⟨Fin.cons (min capacity total) allocation, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Nat.min_le_left capacity total
        · exact hcapacity j
      · rw [Fin.sum_univ_succ]
        simp [hsum, Nat.add_sub_of_le (Nat.min_le_right capacity total)]

theorem binary_group_cardinality (n z : ℕ) : groupedWordSum (1 : ℕ) 1 n z = n.choose z := by
  induction n generalizing z with
  | zero => cases z <;> simp [groupedWordSum_zero]
  | succ n ih =>
      cases z with
      | zero => rw [groupedWordSum_succ_zero, ih]; simp
      | succ z =>
          rw [groupedWordSum_succ_succ, ih, ih]
          simp [Nat.choose_succ_succ]

theorem exists_projected_group_allocation (depth zeros total : ℕ)
    (h : total ≤ depth.choose zeros * 2 ^ zeros) :
    ∃ allocation : Fin (depth.choose zeros) → ℕ,
      (∀ i, allocation i ≤ 2 ^ zeros) ∧ (∑ i, allocation i) = total :=
  exists_bounded_allocation _ _ _ h

end Universality.Certificates

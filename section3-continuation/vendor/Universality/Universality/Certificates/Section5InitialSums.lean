import Universality.Certificates.Section5Allocation
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Nodup

namespace Universality.Certificates

def fixedZeroWords (depth zeros : ℕ) : List (List Bool) :=
  (binaryWords depth).filter (fun word => decide (zeroCount word = zeros))

theorem mem_fixedZeroWords {depth zeros : ℕ} {word : List Bool}
    (member : word ∈ fixedZeroWords depth zeros) :
    word.length = depth ∧ zeroCount word = zeros := by
  obtain ⟨length_member, zeros_checked⟩ := List.mem_filter.mp member
  exact ⟨word_length_of_mem_binaryWords length_member, of_decide_eq_true zeros_checked⟩

theorem fixedZeroWords_zero (zeros : ℕ) :
    fixedZeroWords 0 zeros = if zeros = 0 then [[]] else [] := by
  cases zeros <;> simp [fixedZeroWords, binaryWords, zeroCount]

theorem fixedZeroWords_succ_zero (depth : ℕ) :
    fixedZeroWords (depth + 1) 0 = (fixedZeroWords depth 0).map (true :: ·) := by
  simp [fixedZeroWords, binaryWords, List.filter_map, Function.comp_def]

theorem fixedZeroWords_succ_succ (depth zeros : ℕ) :
    fixedZeroWords (depth + 1) (zeros + 1) =
      (fixedZeroWords depth zeros).map (false :: ·) ++
        (fixedZeroWords depth (zeros + 1)).map (true :: ·) := by
  simp [fixedZeroWords, binaryWords, List.filter_map, Function.comp_def]

theorem fixedZeroWords_length (depth zeros : ℕ) :
    (fixedZeroWords depth zeros).length = depth.choose zeros := by
  induction depth generalizing zeros with
  | zero => cases zeros <;> simp [fixedZeroWords_zero]
  | succ depth induction_hypothesis =>
      cases zeros with
      | zero => simp [fixedZeroWords_succ_zero, induction_hypothesis]
      | succ zeros =>
          simp [fixedZeroWords_succ_succ, induction_hypothesis, Nat.choose_succ_succ]

theorem fixedZeroLexRank_map_true (depth zeros : ℕ) :
    ((fixedZeroWords depth zeros).map (true :: ·)).map fixedZeroLexRank =
      ((fixedZeroWords depth zeros).map fixedZeroLexRank).map
        (firstZeroWordCount (depth + 1) zeros + ·) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro word member
  obtain ⟨length_checked, zeros_checked⟩ := mem_fixedZeroWords member
  simp [Function.comp_def, fixedZeroLexRank, length_checked, zeros_checked]

theorem fixedZeroLexRank_range (depth zeros : ℕ) :
    (fixedZeroWords depth zeros).map fixedZeroLexRank = List.range (depth.choose zeros) := by
  induction depth generalizing zeros with
  | zero => cases zeros <;> simp [fixedZeroWords_zero, fixedZeroLexRank]
  | succ depth induction_hypothesis =>
      cases zeros with
      | zero =>
          rw [fixedZeroWords_succ_zero, fixedZeroLexRank_map_true, induction_hypothesis]
          simp [firstZeroWordCount]
      | succ zeros =>
          rw [fixedZeroWords_succ_succ, List.map_append, fixedZeroLexRank_map_true]
          have falseMap (words : List (List Bool)) :
              (words.map (false :: ·)).map fixedZeroLexRank = words.map fixedZeroLexRank := by
            simp [List.map_map, Function.comp_def, fixedZeroLexRank]
          rw [falseMap]
          rw [induction_hypothesis, induction_hypothesis]
          simp only [firstZeroWordCount, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            ↓reduceIte, Nat.add_sub_cancel, binomialByRatio_eq_choose,
            Nat.choose_succ_succ, List.range_add]

private theorem sum_range_indicator (size cutoff : ℕ) :
    ((List.range size).map fun rank => if rank < cutoff then 1 else 0).sum = min size cutoff := by
  induction size with
  | zero => simp
  | succ size induction_hypothesis =>
      simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, induction_hypothesis]
      split_ifs <;> omega

theorem fixedZeroLexRank_prefix_count (depth zeros cutoff : ℕ) :
    ((fixedZeroWords depth zeros).map fun word =>
      if fixedZeroLexRank word < cutoff then 1 else 0).sum = min (depth.choose zeros) cutoff := by
  have mapped := congrArg (fun ranks : List ℕ =>
    (ranks.map fun rank => if rank < cutoff then 1 else 0).sum)
    (fixedZeroLexRank_range depth zeros)
  simpa only [List.map_map, Function.comp_def, sum_range_indicator] using mapped

theorem fixedZeroWords_head_sum (depth zeros firstFalse firstTrue : ℕ) :
    ((fixedZeroWords (depth + 1) zeros).map fun word =>
      if word.headD false then firstTrue else firstFalse).sum =
      firstZeroWordCount (depth + 1) zeros * firstFalse + depth.choose zeros * firstTrue := by
  cases zeros with
  | zero =>
      simp [fixedZeroWords_succ_zero, List.map_map, Function.comp_def, firstZeroWordCount,
        fixedZeroWords_length]
  | succ zeros =>
      simp [fixedZeroWords_succ_succ, List.map_append, List.map_map, Function.comp_def,
        firstZeroWordCount, binomialByRatio_eq_choose, fixedZeroWords_length]

theorem initialAllocation_fixed_zero_sum (rows : List InitialAllocationRow)
    (depth zeros : ℕ) (remainder_bound : (rows[zeros]!).remainder ≤ (depth + 1).choose zeros) :
    ((fixedZeroWords (depth + 1) zeros).map (initialAllocation rows)).sum =
      firstZeroWordCount (depth + 1) zeros * (rows[zeros]!).firstFalse +
      depth.choose zeros * (rows[zeros]!).firstTrue + (rows[zeros]!).remainder := by
  have terms : (fixedZeroWords (depth + 1) zeros).map (initialAllocation rows) =
      (fixedZeroWords (depth + 1) zeros).map (fun word =>
        (if word.headD false then (rows[zeros]!).firstTrue else (rows[zeros]!).firstFalse) +
          if fixedZeroLexRank word < (rows[zeros]!).remainder then 1 else 0) := by
    apply List.map_congr_left
    intro word member
    simp only [initialAllocation, (mem_fixedZeroWords member).2]
  rw [terms, List.sum_map_add, fixedZeroWords_head_sum, fixedZeroLexRank_prefix_count,
    min_eq_right remainder_bound]

private theorem list_sum_filtered {α M : Type*} [AddCommMonoid M]
    (words : List α) (predicate : α → Bool) (value : α → M) :
    ((words.filter predicate).map value).sum =
      (words.map fun word => if predicate word then value word else 0).sum := by
  induction words with
  | nil => simp
  | cons word words induction_hypothesis =>
      cases checked : predicate word <;> simp [checked, induction_hypothesis]

theorem fixedZeroWords_word_sum {R : Type*} [Semiring R] (outer central : R)
    (depth zeros : ℕ) :
    ((fixedZeroWords depth zeros).map (wordProduct outer central)).sum =
      groupedWordSum outer central depth zeros := by
  rw [fixedZeroWords, list_sum_filtered]
  simp only [decide_eq_true_eq, groupedWordSum]

/-- Exact ordered prefix sum; the cutoff is the zero-based lexicographic rank. -/
def lexPrefixWordSum {R : Type*} [Semiring R] (outer central : R)
    (depth zeros cutoff : ℕ) : R :=
  ((fixedZeroWords depth zeros).map fun word =>
    if fixedZeroLexRank word < cutoff then wordProduct outer central word else 0).sum

theorem lexPrefixWordSum_cutoff_zero {R : Type*} [Semiring R] (outer central : R)
    (depth zeros : ℕ) : lexPrefixWordSum outer central depth zeros 0 = 0 := by
  simp [lexPrefixWordSum]

theorem lexPrefixWordSum_depth_zero {R : Type*} [Semiring R] (outer central : R)
    (zeros cutoff : ℕ) :
    lexPrefixWordSum outer central 0 zeros cutoff = if zeros = 0 ∧ 0 < cutoff then 1 else 0 := by
  by_cases zero : zeros = 0 <;>
    simp [lexPrefixWordSum, fixedZeroWords_zero, zero, fixedZeroLexRank, wordProduct]

theorem lexPrefixWordSum_full {R : Type*} [Semiring R] (outer central : R)
    (depth zeros cutoff : ℕ) (covers : depth.choose zeros ≤ cutoff) :
    lexPrefixWordSum outer central depth zeros cutoff = groupedWordSum outer central depth zeros := by
  rw [← fixedZeroWords_word_sum]
  unfold lexPrefixWordSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro word member
  have rank_member : fixedZeroLexRank word ∈ (fixedZeroWords depth zeros).map fixedZeroLexRank :=
    List.mem_map.mpr ⟨word, member, rfl⟩
  rw [fixedZeroLexRank_range] at rank_member
  have below : fixedZeroLexRank word < cutoff :=
    lt_of_lt_of_le (List.mem_range.mp rank_member) covers
  simp [below]

theorem lexPrefixWordSum_succ_zero {R : Type*} [Semiring R] (outer central : R)
    (depth cutoff : ℕ) :
    lexPrefixWordSum outer central (depth + 1) 0 cutoff =
      central * lexPrefixWordSum outer central depth 0 cutoff := by
  unfold lexPrefixWordSum
  rw [fixedZeroWords_succ_zero, List.map_map, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro word member
  obtain ⟨length_checked, zeros_checked⟩ := mem_fixedZeroWords member
  simp [Function.comp_def, fixedZeroLexRank, firstZeroWordCount, zeros_checked,
    wordProduct, mul_ite]

theorem lexPrefixWordSum_succ_succ {R : Type*} [Semiring R] (outer central : R)
    (depth zeros cutoff : ℕ) :
    lexPrefixWordSum outer central (depth + 1) (zeros + 1) cutoff =
      outer * lexPrefixWordSum outer central depth zeros cutoff +
        central * lexPrefixWordSum outer central depth (zeros + 1) (cutoff - depth.choose zeros) := by
  unfold lexPrefixWordSum
  rw [fixedZeroWords_succ_succ, List.map_append, List.sum_append, List.map_map, List.map_map]
  congr 1
  · rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro word _
    simp [Function.comp_def, fixedZeroLexRank, wordProduct, mul_ite]
  · rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro word member
    obtain ⟨length_checked, zeros_checked⟩ := mem_fixedZeroWords member
    have comparison : depth.choose zeros + fixedZeroLexRank word < cutoff ↔
        fixedZeroLexRank word < cutoff - depth.choose zeros := by omega
    simp [Function.comp_def, fixedZeroLexRank, firstZeroWordCount,
      length_checked, zeros_checked, binomialByRatio_eq_choose, comparison, wordProduct, mul_ite]

/-- The compressed lex-prefix recurrence, with the first complete block replaced
by its grouped sum when the cutoff passes that block. -/
theorem lexPrefixWordSum_split {R : Type*} [Semiring R] (outer central : R)
    (depth zeros cutoff : ℕ) :
    lexPrefixWordSum outer central (depth + 1) (zeros + 1) cutoff =
      if cutoff ≤ depth.choose zeros then outer * lexPrefixWordSum outer central depth zeros cutoff
      else outer * groupedWordSum outer central depth zeros +
        central * lexPrefixWordSum outer central depth (zeros + 1) (cutoff - depth.choose zeros) := by
  rw [lexPrefixWordSum_succ_succ]
  by_cases firstBlock : cutoff ≤ depth.choose zeros
  · simp [firstBlock, Nat.sub_eq_zero_of_le firstBlock, lexPrefixWordSum_cutoff_zero]
  · rw [if_neg firstBlock, lexPrefixWordSum_full outer central depth zeros cutoff (by omega)]

private theorem initial_sum_swap_lists {α β M : Type*} [AddCommMonoid M]
    (first : List α) (second : List β) (value : α → β → M) :
    (first.map fun a => (second.map (value a)).sum).sum =
      (second.map fun b => (first.map fun a => value a b).sum).sum := by
  induction first with
  | nil => simp
  | cons a first induction_hypothesis =>
      simp only [List.map_cons, List.sum_cons, induction_hypothesis, List.sum_map_add]

theorem sum_grouped_zeroCount {M : Type*} [AddCommMonoid M]
    (depth : ℕ) (value : List Bool → M) :
    ((binaryWords depth).map value).sum =
      ((List.range (depth + 1)).map fun zeros =>
        ((fixedZeroWords depth zeros).map value).sum).sum := by
  have expand (word : List Bool) (member : word ∈ binaryWords depth) :
      value word = ((List.range (depth + 1)).map fun zeros =>
        if zeroCount word = zeros then value word else 0).sum := by
    symm
    rw [List.sum_map_eq_nsmul_single (zeroCount word)]
    · have count_member : zeroCount word ∈ List.range (depth + 1) := by
        simp only [List.mem_range]
        have bound := zeroCount_le_length word
        have length_checked := word_length_of_mem_binaryWords member
        omega
      rw [List.count_eq_one_of_mem List.nodup_range count_member]
      simp
    · intro zeros different _
      simp [Ne.symm different]
  have map_equality : (binaryWords depth).map value =
      (binaryWords depth).map (fun word => ((List.range (depth + 1)).map fun zeros =>
        if zeroCount word = zeros then value word else 0).sum) := by
    apply List.map_congr_left
    exact expand
  rw [map_equality, initial_sum_swap_lists]
  apply congrArg List.sum
  apply List.map_congr_left
  intro zeros _
  simp only [fixedZeroWords, list_sum_filtered, decide_eq_true_eq]

theorem initialAllocation_grouped_moment (rows : List InitialAllocationRow)
    (depth : ℕ) (weight : ℕ → ℤ)
    (remainder_bound : ∀ zeros ∈ List.range (depth + 2),
      (rows[zeros]!).remainder ≤ (depth + 1).choose zeros) :
    ((binaryWords (depth + 1)).map fun word =>
      (initialAllocation rows word : ℤ) * weight (zeroCount word)).sum =
      ((List.range (depth + 2)).map fun zeros =>
        ((firstZeroWordCount (depth + 1) zeros * (rows[zeros]!).firstFalse +
          depth.choose zeros * (rows[zeros]!).firstTrue + (rows[zeros]!).remainder : ℕ) : ℤ) *
            weight zeros).sum := by
  rw [sum_grouped_zeroCount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro zeros member
  have terms : ((fixedZeroWords (depth + 1) zeros).map fun word =>
      (initialAllocation rows word : ℤ) * weight (zeroCount word)) =
      ((fixedZeroWords (depth + 1) zeros).map fun word =>
        (initialAllocation rows word : ℤ) * weight zeros) := by
    apply List.map_congr_left
    intro word word_member
    rw [(mem_fixedZeroWords word_member).2]
  rw [terms, List.sum_map_mul_right]
  have cast_sum : ((fixedZeroWords (depth + 1) zeros).map fun word =>
      (initialAllocation rows word : ℤ)).sum =
      (((fixedZeroWords (depth + 1) zeros).map (initialAllocation rows)).sum : ℕ) := by
    simp only [Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [cast_sum, initialAllocation_fixed_zero_sum rows depth zeros (remainder_bound zeros member)]

theorem fixedZeroWords_firstBit_word_sum {R : Type*} [Semiring R]
    (outer central : R) (depth zeros firstFalse firstTrue : ℕ) :
    ((fixedZeroWords (depth + 1) zeros).map fun word =>
      ((if word.headD false then firstTrue else firstFalse : ℕ) : R) *
        wordProduct outer central word).sum =
      (firstFalse : R) * (if zeros = 0 then 0 else outer * groupedWordSum outer central depth (zeros - 1)) +
        (firstTrue : R) * (central * groupedWordSum outer central depth zeros) := by
  cases zeros with
  | zero =>
      simp only [fixedZeroWords_succ_zero, List.map_map, Function.comp_def, List.headD_cons,
        Bool.true_eq, ↓reduceIte, wordProduct, mul_zero, zero_add]
      rw [List.sum_map_mul_left, List.sum_map_mul_left, fixedZeroWords_word_sum]
  | succ zeros =>
      simp only [fixedZeroWords_succ_succ, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, List.headD_cons, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
        wordProduct, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
      rw [List.sum_map_mul_left, List.sum_map_mul_left, fixedZeroWords_word_sum,
        List.sum_map_mul_left, List.sum_map_mul_left, fixedZeroWords_word_sum]

theorem initialAllocation_fixed_zero_word_sum {R : Type*} [Semiring R]
    (outer central : R) (rows : List InitialAllocationRow) (depth zeros : ℕ) :
    ((fixedZeroWords (depth + 1) zeros).map fun word =>
      (initialAllocation rows word : R) * wordProduct outer central word).sum =
      ((rows[zeros]!).firstFalse : R) *
        (if zeros = 0 then 0 else outer * groupedWordSum outer central depth (zeros - 1)) +
      ((rows[zeros]!).firstTrue : R) * (central * groupedWordSum outer central depth zeros) +
      lexPrefixWordSum outer central (depth + 1) zeros (rows[zeros]!).remainder := by
  have terms : ((fixedZeroWords (depth + 1) zeros).map fun word =>
      (initialAllocation rows word : R) * wordProduct outer central word) =
      ((fixedZeroWords (depth + 1) zeros).map fun word =>
        ((if word.headD false then (rows[zeros]!).firstTrue else (rows[zeros]!).firstFalse : ℕ) : R) *
          wordProduct outer central word +
        if fixedZeroLexRank word < (rows[zeros]!).remainder then wordProduct outer central word else 0) := by
    apply List.map_congr_left
    intro word member
    simp only [initialAllocation, (mem_fixedZeroWords member).2, Nat.cast_add, add_mul]
    split_ifs <;> simp
  rw [terms, List.sum_map_add, fixedZeroWords_firstBit_word_sum]
  rfl

theorem initialAllocation_ordered_word_sum {R : Type*} [Semiring R]
    (outer central : R) (rows : List InitialAllocationRow) (depth : ℕ) :
    ((binaryWords (depth + 1)).map fun word =>
      (initialAllocation rows word : R) * wordProduct outer central word).sum =
      ((List.range (depth + 2)).map fun zeros =>
        ((rows[zeros]!).firstFalse : R) *
          (if zeros = 0 then 0 else outer * groupedWordSum outer central depth (zeros - 1)) +
        ((rows[zeros]!).firstTrue : R) * (central * groupedWordSum outer central depth zeros) +
        lexPrefixWordSum outer central (depth + 1) zeros (rows[zeros]!).remainder).sum := by
  rw [sum_grouped_zeroCount]
  simp only [initialAllocation_fixed_zero_word_sum]

end Universality.Certificates

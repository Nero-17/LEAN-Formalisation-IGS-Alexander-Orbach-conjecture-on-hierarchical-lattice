import Universality.Algebra.PacketCancellation
import Universality.Algebra.GroupedWords
import Mathlib.Data.List.TakeDrop

/-!
# The actual signed correction supports of Section 5

The four tails are a first bit followed by a constant word.  Odd numbers of
opposite pairs precede these tails.  The number of initial opposite pairs
locates a support uniquely, including the final layer whose tails have length
two.  Thus bounds checked for individual packets really cover their sum.
-/

namespace Universality.Certificates

def initialOppositePairs : List Bool → ℕ
  | first :: second :: rest =>
      if first = second then 0 else initialOppositePairs rest + 1
  | _ => 0

def correctionTail (first repeated : Bool) (remaining : ℕ) : List Bool :=
  first :: List.replicate (remaining + 1) repeated

theorem initialOppositePairs_replicate (bit : Bool) (count : ℕ) :
    initialOppositePairs (List.replicate count bit) = 0 := by
  rcases count with _ | _ | count <;> simp [List.replicate_succ, initialOppositePairs]

theorem initialOppositePairs_tail_le (first repeated : Bool) (remaining : ℕ) :
    initialOppositePairs (correctionTail first repeated remaining) ≤ 1 := by
  simp only [correctionTail, List.replicate_succ, initialOppositePairs,
    initialOppositePairs_replicate]
  split <;> omega

theorem correctionTail_length (first repeated : Bool) (remaining : ℕ) :
    (correctionTail first repeated remaining).length = remaining + 2 := by
  simp [correctionTail, Nat.add_assoc]

theorem correctionTail_injective {first repeated first' repeated' : Bool}
    {remaining remaining' : ℕ}
    (equal : correctionTail first repeated remaining =
      correctionTail first' repeated' remaining') :
    first = first' ∧ repeated = repeated' ∧ remaining = remaining' := by
  have lengths := congrArg List.length equal
  simp only [correctionTail_length] at lengths
  have remaining_equal : remaining = remaining' := by omega
  subst remaining'
  simp only [correctionTail, List.replicate_succ, List.cons.injEq] at equal
  exact ⟨equal.1, equal.2.1, rfl⟩

theorem initialOppositePairs_paired_append (choices tail : List Bool) :
    initialOppositePairs (pairedWord choices ++ tail) =
      choices.length + initialOppositePairs tail := by
  induction choices with
  | nil => simp [pairedWord]
  | cons bit choices induction_hypothesis =>
      cases bit <;>
        simp [pairedWord, initialOppositePairs, induction_hypothesis, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]

theorem pairedWord_zeroCount (choices : List Bool) :
    zeroCount (pairedWord choices) = choices.length := by
  induction choices with
  | nil => rfl
  | cons bit choices induction_hypothesis =>
      cases bit <;> simp [pairedWord, induction_hypothesis]

theorem pairedWord_injective : Function.Injective pairedWord := by
  intro choices
  induction choices with
  | nil =>
      intro choices' equal
      cases choices' with
      | nil => rfl
      | cons bit choices' => cases bit <;> simp [pairedWord] at equal
  | cons bit choices induction_hypothesis =>
      intro choices' equal
      cases choices' with
      | nil => cases bit <;> simp [pairedWord] at equal
      | cons bit' choices' =>
          cases bit <;> cases bit' <;> simp only [pairedWord, List.cons.injEq] at equal
          · exact congrArg (false :: ·) (induction_hypothesis equal.2.2)
          · exact False.elim (Bool.false_ne_true equal.1)
          · exact False.elim (Bool.false_ne_true equal.1.symm)
          · exact congrArg (true :: ·) (induction_hypothesis equal.2.2)

/-- Equality of two correction words forces equality of their layer indices.
There is no assumption about the total depth, so this covers every supplied
certificate and, in particular, the last layer. -/
theorem correction_layer_unique {layer layer' : ℕ} {choices choices' : List Bool}
    {first repeated first' repeated' : Bool} {remaining remaining' : ℕ}
    (choice_length : choices.length = 2 * layer + 1)
    (choice_length' : choices'.length = 2 * layer' + 1)
    (equal : pairedWord choices ++ correctionTail first repeated remaining =
      pairedWord choices' ++ correctionTail first' repeated' remaining') :
    layer = layer' := by
  have pair_counts := congrArg initialOppositePairs equal
  rw [initialOppositePairs_paired_append, initialOppositePairs_paired_append,
    choice_length, choice_length'] at pair_counts
  have tail_bound := initialOppositePairs_tail_le first repeated remaining
  have tail_bound' := initialOppositePairs_tail_le first' repeated' remaining'
  omega

theorem correction_support_unique {layer layer' : ℕ} {choices choices' : List Bool}
    {first repeated first' repeated' : Bool} {remaining remaining' : ℕ}
    (choice_length : choices.length = 2 * layer + 1)
    (choice_length' : choices'.length = 2 * layer' + 1)
    (equal : pairedWord choices ++ correctionTail first repeated remaining =
      pairedWord choices' ++ correctionTail first' repeated' remaining') :
    layer = layer' ∧ choices = choices' ∧ first = first' ∧
      repeated = repeated' ∧ remaining = remaining' := by
  have layer_equal := correction_layer_unique choice_length choice_length' equal
  subst layer'
  have prefix_length : (pairedWord choices).length = (pairedWord choices').length := by
    simp only [pairedWord_length, choice_length, choice_length']
  have split_equal := List.append_inj equal prefix_length
  exact ⟨rfl, pairedWord_injective split_equal.1,
    correctionTail_injective split_equal.2⟩

theorem wordSign_unit (choices : List Bool) : wordSign choices = 1 ∨ wordSign choices = -1 := by
  induction choices with
  | nil => exact Or.inl rfl
  | cons bit choices induction_hypothesis =>
      cases bit
      · exact induction_hypothesis
      · rcases induction_hypothesis with positive | negative
        · exact Or.inr (by simp [wordSign, positive])
        · exact Or.inl (by simp [wordSign, negative])

theorem wordSign_abs (choices : List Bool) : |wordSign choices| = 1 := by
  rcases wordSign_unit choices with positive | negative
  · simp [positive]
  · simp [negative]

theorem wordSign_sum_succ (count : ℕ) :
    ((binaryWords (count + 1)).map wordSign).sum = 0 := by
  simp only [binaryWords, List.map_append, List.map_map, Function.comp_def, wordSign,
    List.sum_append]
  have negated (words : List (List Bool)) :
      (words.map fun word => -wordSign word).sum = -(words.map wordSign).sum := by
    induction words with
    | nil => simp
    | cons word words induction_hypothesis => simp [induction_hypothesis, add_comm]
  rw [negated]
  exact add_neg_cancel _

theorem correction_fixed_zeroCount (choices tail : List Bool) :
    zeroCount (pairedWord choices ++ tail) = choices.length + zeroCount tail := by
  simp only [zeroCount, List.count_append]
  exact congrArg (· + zeroCount tail) (pairedWord_zeroCount choices)

/-- Every packet has zero total at its (single) zero count. -/
theorem correction_scalar_sum (coefficient : ℤ) (count : ℕ) (tail : List Bool)
    (weight : ℕ → ℤ) :
    ((binaryWords (count + 1)).map fun choices =>
      coefficient * wordSign choices * weight (zeroCount (pairedWord choices ++ tail))).sum = 0 := by
  calc
    _ = ((binaryWords (count + 1)).map fun choices =>
        coefficient * wordSign choices * weight (count + 1 + zeroCount tail)).sum := by
      congr 1
      apply List.map_congr_left
      intro choices member
      rw [correction_fixed_zeroCount, word_length_of_mem_binaryWords member]
    _ = 0 := by
      rw [List.sum_map_mul_right, List.sum_map_mul_left, wordSign_sum_succ]
      simp

theorem correction_capacity_of_slack (initial capacity coefficient slack : ℤ)
    (choices : List Bool) (lower : slack ≤ initial) (upper : initial + slack ≤ capacity)
    (coefficient_bound : |coefficient| ≤ slack) :
    0 ≤ initial + coefficient * wordSign choices ∧
      initial + coefficient * wordSign choices ≤ capacity := by
  have coefficient_lower := (abs_le.mp coefficient_bound).1
  have coefficient_upper := (abs_le.mp coefficient_bound).2
  rcases wordSign_unit choices with positive | negative
  · rw [positive, mul_one]
    omega
  · rw [negative, mul_neg_one]
    omega

/-- Exact mass repair, retaining the order of every kernel factor. -/
theorem correction_mass_sum (coefficient : ℤ) (layer : ℕ) (tail : List Bool)
    (rightFactor : Matrix (Fin 2) (Fin 2) ℤ) :
    ((binaryWords (2 * layer + 1)).map fun choices =>
      (coefficient * wordSign choices) •
        (wordProduct outerKernelNumerator centralKernelNumerator
          (pairedWord choices ++ tail) * rightFactor)).sum =
      (coefficient * 18 ^ layer) •
        (!![-6, -6; 3, 6] *
          wordProduct outerKernelNumerator centralKernelNumerator tail * rightFactor) := by
  simp_rw [wordProduct_append, mul_assoc, mul_smul]
  simp_rw [← smul_mul_assoc]
  rw [List.sum_map_mul_right]
  have scalar_sum (words : List (List Bool)) :
      (words.map fun choices => coefficient •
        (wordSign choices • wordProduct outerKernelNumerator centralKernelNumerator
          (pairedWord choices))).sum =
      coefficient • (words.map fun choices => wordSign choices •
        wordProduct outerKernelNumerator centralKernelNumerator (pairedWord choices)).sum := by
    induction words with
    | nil => simp
    | cons word words induction_hypothesis =>
        simp only [List.map_cons, List.sum_cons, induction_hypothesis, smul_add]
  rw [scalar_sum, signed_wheatstone_packet]

end Universality.Certificates

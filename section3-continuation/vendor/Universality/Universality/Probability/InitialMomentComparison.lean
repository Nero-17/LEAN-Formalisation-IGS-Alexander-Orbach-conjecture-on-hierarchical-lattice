import Universality.Probability.MomentOperatorComparison

namespace Universality
noncomputable section
variable {ι Ω J : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Ω] [DecidableEq Ω] [Fintype J] [DecidableEq J]

theorem branchingMomentOperator_congr_upto (weight reward : ι → Ω → ℝ)
    (children : ι → Ω → J → Option ι) (first second : ι → ℕ → ℝ) (order : ℕ)
    (heq : ∀ state k, k ≤ order → first state k = second state k) (state : ι) :
    branchingMomentOperator weight reward children first order state =
      branchingMomentOperator weight reward children second order state := by
  unfold branchingMomentOperator
  apply Finset.sum_congr rfl
  intro configuration _
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  unfold assignmentMomentSum
  apply Finset.sum_congr rfl
  intro assignment _
  apply Finset.prod_congr rfl
  intro child _
  have hcard : Fintype.card {a : Fin k // assignment a = child} ≤ order :=
    (Fintype.card_subtype_le _).trans (by simpa only [Fintype.card_fin] using Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  cases hchild : children state configuration child with
  | none => simp only [hchild, branchingChildMoment]
  | some next => simpa only [hchild, branchingChildMoment] using heq next _ hcard

theorem branchingMomentOperator_scale_comparison_upto
    (weight reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι)
    (first second : ι → ℕ → ℝ)
    (hweight : ∀ state configuration, 0 ≤ weight state configuration)
    (hreward : ∀ state configuration, 0 ≤ reward state configuration)
    (hfirst : ∀ state order, 0 ≤ first state order)
    (hsecond : ∀ state order, 0 ≤ second state order)
    (scale : ℝ) (hscale : 1 ≤ scale) (order : ℕ) (horder : 1 ≤ order)
    (hbound : ∀ state k, k ≤ order → first state k ≤ scale ^ k * second state k) (state : ι) :
    branchingMomentOperator weight reward children first order state ≤
      scale ^ order * branchingMomentOperator weight reward children second order state := by
  let firstTruncated : ι → ℕ → ℝ := fun state k => if k ≤ order then first state k else 0
  let secondTruncated : ι → ℕ → ℝ := fun state k => if k ≤ order then second state k else 0
  have hfirstEq := branchingMomentOperator_congr_upto weight reward children first firstTruncated order
    (by intro state k hk; simp [firstTruncated, hk]) state
  have hsecondEq := branchingMomentOperator_congr_upto weight reward children second secondTruncated order
    (by intro state k hk; simp [secondTruncated, hk]) state
  rw [hfirstEq, hsecondEq]
  have hb := branchingMomentOperator_scale_comparison weight weight reward children firstTruncated secondTruncated
    hweight hweight hreward
    (by intro state k; dsimp [firstTruncated]; split; exact hfirst _ _; exact le_rfl)
    (by intro state k; dsimp [secondTruncated]; split; exact hsecond _ _; exact le_rfl)
    1 scale le_rfl hscale (by intro state configuration; simp)
    (by
      intro state k
      by_cases hk : k ≤ order
      · simpa only [firstTruncated, secondTruncated, hk, ↓reduceIte] using hbound state k hk
      · simp [firstTruncated, secondTruncated, hk]) order horder state
  simpa only [one_mul] using hb

/-- An initial graded bound is propagated without further loss when the
subsequent configuration laws coincide. Only orders up to the requested one
are assumed, allowing finite-order post-exit estimates. -/
theorem branching_moment_initial_comparison
    (weight : ℕ → ι → Ω → ℝ) (reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι)
    (first second : ℕ → ι → ℕ → ℝ)
    (hweight : ∀ n state configuration, 0 ≤ weight n state configuration)
    (hreward : ∀ state configuration, 0 ≤ reward state configuration)
    (hfirst : ∀ n state order, 0 ≤ first n state order)
    (hsecond : ∀ n state order, 0 ≤ second n state order)
    (hfirstZero : ∀ n state, first n state 0 = 1)
    (hsecondZero : ∀ n state, second n state 0 = 1)
    (scale : ℝ) (hscale : 1 ≤ scale) (order : ℕ)
    (hbase : ∀ state k, k ≤ order → first 0 state k ≤ scale ^ k * second 0 state k)
    (hfirstRecursion : ∀ n state k, first (n + 1) state k =
      branchingMomentOperator (weight n) reward children (first n) k state)
    (hsecondRecursion : ∀ n state k, second (n + 1) state k =
      branchingMomentOperator (weight n) reward children (second n) k state) :
    ∀ n state k, k ≤ order → first n state k ≤ scale ^ k * second n state k := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro state k hk
    by_cases hzero : k = 0
    · simp [hzero, hfirstZero, hsecondZero]
    rw [hfirstRecursion, hsecondRecursion]
    exact branchingMomentOperator_scale_comparison_upto (weight n) reward children (first n) (second n)
      (hweight n) hreward (hfirst n) (hsecond n) scale hscale k (by omega)
      (fun state j hj => ih state j (hj.trans hk)) state

end
end Universality


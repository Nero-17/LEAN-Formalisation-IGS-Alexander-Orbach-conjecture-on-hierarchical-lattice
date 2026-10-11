import Universality.Probability.MomentOperatorComparison

namespace Universality
noncomputable section
variable {ι Ω J : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Ω] [DecidableEq Ω] [Fintype J] [DecidableEq J]

/-- A graded moment comparison for a finite sequence of genuinely varying
configuration laws, requiring no independence between rewards and child types. -/
theorem inhomogeneous_branching_moment_comparison
    (weight referenceWeight : ℕ → ι → Ω → ℝ) (reward : ι → Ω → ℝ)
    (children : ι → Ω → J → Option ι) (moments referenceMoments : ℕ → ι → ℕ → ℝ)
    (factor : ℕ → ℝ) (depth : ℕ)
    (hfactor : ∀ n ≤ depth, 1 ≤ factor n)
    (hweight : ∀ n ≤ depth, ∀ state configuration, 0 ≤ weight n state configuration)
    (hreferenceWeight : ∀ n ≤ depth, ∀ state configuration, 0 ≤ referenceWeight n state configuration)
    (hreward : ∀ state configuration, 0 ≤ reward state configuration)
    (hmoments : ∀ n state order, 0 ≤ moments n state order)
    (hreferenceMoments : ∀ n state order, 0 ≤ referenceMoments n state order)
    (hzero : ∀ n state, moments n state 0 = 1)
    (hreferenceZero : ∀ n state, referenceMoments n state 0 = 1)
    (hweightComparison : ∀ n ≤ depth, ∀ state configuration,
      weight n state configuration ≤ factor n * referenceWeight n state configuration)
    (hbase : ∀ state order, moments 0 state order ≤ factor 0 ^ order * referenceMoments 0 state order)
    (hrecursion : ∀ n state order, moments (n + 1) state order =
      branchingMomentOperator (weight (n + 1)) reward children (moments n) order state)
    (hreferenceRecursion : ∀ n state order, referenceMoments (n + 1) state order =
      branchingMomentOperator (referenceWeight (n + 1)) reward children (referenceMoments n) order state) :
    ∀ n ≤ depth, ∀ state order, moments n state order ≤
      (∏ j ∈ Finset.range (n + 1), factor j) ^ order * referenceMoments n state order := by
  intro n
  induction n with
  | zero => simpa using fun (_ : 0 ≤ depth) => hbase
  | succ n ih =>
    intro hn state order
    by_cases horder : order = 0
    · simp [horder, hzero, hreferenceZero]
    have hscale : 1 ≤ ∏ j ∈ Finset.range (n + 1), factor j := by
      apply Finset.one_le_prod
      intro j hj
      exact hfactor j (by have := Finset.mem_range.mp hj; omega)
    rw [hrecursion, hreferenceRecursion]
    have hb := branchingMomentOperator_scale_comparison (weight (n + 1)) (referenceWeight (n + 1)) reward children
      (moments n) (referenceMoments n) (hweight (n + 1) hn) (hreferenceWeight (n + 1) hn) hreward
      (hmoments n) (hreferenceMoments n) (factor (n + 1)) (∏ j ∈ Finset.range (n + 1), factor j)
      (hfactor (n + 1) hn) hscale (hweightComparison (n + 1) hn) (ih (by omega)) order (by omega) state
    simpa only [Finset.prod_range_succ, mul_comm (factor (n + 1))] using hb

end
end Universality

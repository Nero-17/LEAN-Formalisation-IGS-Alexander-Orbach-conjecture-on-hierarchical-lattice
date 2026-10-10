import Universality.Probability.BranchingMomentBounds

namespace Universality
noncomputable section
open Matrix
set_option maxHeartbeats 0

/-- All integer moments of a bounded finite-type reward recursion. The
recursion, normalized zeroth moments, and first-moment bound are hypotheses;
no higher-order growth assertion is assumed. -/
theorem branching_all_moment_bounds {ι Ω J : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Ω] [DecidableEq Ω] [Fintype J] [DecidableEq J]
    (weight reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι)
    (M : Matrix ι ι ℝ) (eigenweight : ι → ℝ) (radius : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (heigenweight : ∀ i, 0 < eigenweight i)
    (hradius : 1 < radius) (heigen : M *ᵥ eigenweight = radius • eigenweight)
    (hweight : ∀ state configuration, 0 ≤ weight state configuration)
    (hreward : ∀ state configuration, 0 ≤ reward state configuration)
    (hlinear : ∀ values state, (∑ configuration, weight state configuration *
      ∑ child, match children state configuration child with | none => 0 | some other => values other) =
        (M *ᵥ values) state)
    (moments : ℕ → ι → ℕ → ℝ)
    (hnonneg : ∀ n state r, 0 ≤ moments n state r)
    (hzero : ∀ n state, moments n state 0 = 1)
    (hfirst : ∃ bound : ℝ, 0 < bound ∧ ∀ n state, moments n state 1 ≤ bound * radius ^ n)
    (hrecursion : ∀ n r state, moments (n + 1) state r =
      branchingMomentOperator weight reward children (moments n) r state) :
    ∀ r : ℕ, ∃ bound : ℝ, 0 < bound ∧ ∀ n state, moments n state r ≤ bound * radius ^ (r * n) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hzeroOrder : r = 0
    · subst r
      exact ⟨1, zero_lt_one, by simp [hzero]⟩
    by_cases honeOrder : r = 1
    · subst r
      simpa using hfirst
    have hr : 1 < r := by omega
    have hlower : ∀ k : Fin r, ∃ bound : ℝ, 0 < bound ∧
        ∀ n state, moments n state k.val ≤ bound * radius ^ (k.val * n) :=
      fun k => ih k.val k.isLt
    choose bounds hpositive hbounds using hlower
    let constant := 1 + ∑ k : Fin r, bounds k
    have hconstant : 1 ≤ constant := by
      dsimp [constant]
      linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => (hpositive k).le)]
    have hbound (n : ℕ) (state : ι) (k : ℕ) (hk : k < r) :
        moments n state k ≤ constant * radius ^ (k * n) := by
      apply (hbounds ⟨k, hk⟩ n state).trans
      apply mul_le_mul_of_nonneg_right _ (pow_pos (lt_trans zero_lt_one hradius) _).le
      have hsingle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hpositive j).le)
        (Finset.mem_univ (⟨k, hk⟩ : Fin r))
      dsimp [constant]
      linarith
    let forcing := (∑ state : ι, |branchingRemainderCoefficient (J := J) weight reward r state|) *
      constant ^ Fintype.card J
    have hforcing : 0 ≤ forcing := mul_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (pow_nonneg (le_trans zero_le_one hconstant) _)
    have hremainder (n : ℕ) (state : ι) :
        branchingMomentRemainder weight reward children (moments n) r state ≤ forcing * (radius ^ r) ^ n := by
      apply (branchingMomentRemainder_bound weight reward children hweight hreward (moments n)
        constant radius hconstant hradius.le n r (hnonneg n) (hbound n) state).trans
      have hcoefficient : branchingRemainderCoefficient (J := J) weight reward r state ≤
          ∑ other : ι, |branchingRemainderCoefficient (J := J) weight reward r other| :=
        (le_abs_self _).trans (Finset.single_le_sum
          (f := fun other => |branchingRemainderCoefficient (J := J) weight reward r other|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ state))
      dsimp [forcing]
      rw [← mul_assoc, pow_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg (le_trans zero_le_one hconstant) _))
        (pow_pos (pow_pos (lt_trans zero_lt_one hradius) r) n).le
    obtain ⟨bound, hboundPos, hboundAll⟩ := matrix_recursion_exponential_bound M eigenweight
      (fun n state => moments n state r) radius (radius ^ r) forcing hM heigenweight
      (lt_trans zero_lt_one hradius).le (by simpa using pow_lt_pow_right₀ hradius hr)
      hforcing heigen (fun n state => by
        rw [hrecursion, branchingMomentOperator_linear_part weight reward children M hlinear (moments n)
          (hzero n) r (by omega)]
        exact add_le_add le_rfl (hremainder n state))
    exact ⟨bound, hboundPos, by simpa only [pow_mul] using hboundAll⟩

end
end Universality

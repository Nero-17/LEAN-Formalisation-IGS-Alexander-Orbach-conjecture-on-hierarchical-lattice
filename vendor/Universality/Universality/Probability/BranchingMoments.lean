import Universality.Probability.MomentAssignments
import Universality.Matrix.InhomogeneousGrowth

namespace Universality
noncomputable section
open Matrix
set_option maxHeartbeats 0
variable {ι Ω J : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Ω] [DecidableEq Ω] [Fintype J] [DecidableEq J]

def branchingChildMoment (moments : ι → ℕ → ℝ) (child : Option ι) (r : ℕ) : ℝ :=
  match child with
  | none => if r = 0 then 1 else 0
  | some state => moments state r

theorem branchingChildMoment_zero (moments : ι → ℕ → ℝ) (hzero : ∀ state, moments state 0 = 1)
    (child : Option ι) : branchingChildMoment moments child 0 = 1 := by
  cases child <;> simp [branchingChildMoment, hzero]

theorem branchingChildMoment_nonneg (moments : ι → ℕ → ℝ)
    (hnonneg : ∀ state r, 0 ≤ moments state r) (child : Option ι) (r : ℕ) :
    0 ≤ branchingChildMoment moments child r := by
  cases child
  · simp only [branchingChildMoment]; split <;> norm_num
  · exact hnonneg _ _

theorem branchingChildMoment_bound (moments : ι → ℕ → ℝ) (constant radius : ℝ)
    (hconstant : 1 ≤ constant) (hradius : 1 ≤ radius) (n r : ℕ)
    (hbound : ∀ state k, k < r → moments state k ≤ constant * radius ^ (k * n))
    (child : Option ι) (k : ℕ) (hk : k < r) :
    branchingChildMoment moments child k ≤ constant * radius ^ (k * n) := by
  cases child
  · by_cases hzero : k = 0
    · simpa [branchingChildMoment, hzero] using hconstant
    · simp only [branchingChildMoment, hzero, ↓reduceIte]
      exact mul_nonneg (le_trans zero_le_one hconstant) (pow_nonneg (le_trans zero_le_one hradius) _)
  · exact hbound _ _ hk

def branchingMomentOperator (weight reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι)
    (moments : ι → ℕ → ℝ) (r : ℕ) (state : ι) : ℝ :=
  ∑ configuration, weight state configuration *
    ∑ k ∈ Finset.range (r + 1), reward state configuration ^ (r - k) * (r.choose k : ℝ) *
      assignmentMomentSum (fun child => branchingChildMoment moments (children state configuration child)) k

def branchingMomentRemainder (weight reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι)
    (moments : ι → ℕ → ℝ) (r : ℕ) (state : ι) : ℝ :=
  ∑ configuration, weight state configuration *
    ((∑ k ∈ Finset.range r, reward state configuration ^ (r - k) * (r.choose k : ℝ) *
      assignmentMomentSum (fun child => branchingChildMoment moments (children state configuration child)) k) +
      ∑ assignment ∈ (Finset.univ.filter fun assignment : Fin r → J =>
        ¬ ∃ child, assignment = fun _ => child),
        ∏ child, branchingChildMoment moments (children state configuration child)
          (Fintype.card {a : Fin r // assignment a = child}))

theorem branchingMomentOperator_linear_part
    (weight reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι) (M : Matrix ι ι ℝ)
    (hlinear : ∀ values state, (∑ configuration, weight state configuration *
      ∑ child, match children state configuration child with | none => 0 | some other => values other) =
        (M *ᵥ values) state)
    (moments : ι → ℕ → ℝ) (hzero : ∀ state, moments state 0 = 1) (r : ℕ) (hr : 0 < r) (state : ι) :
    branchingMomentOperator weight reward children moments r state =
      (M *ᵥ (fun other => moments other r)) state +
        branchingMomentRemainder weight reward children moments r state := by
  unfold branchingMomentOperator
  simp only [Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul]
  simp_rw [assignmentMomentSum_linear_part _
    (fun child => branchingChildMoment_zero moments hzero (children state _ child)) r hr]
  have hchild (configuration : Ω) (child : J) :
      branchingChildMoment moments (children state configuration child) r =
        match children state configuration child with | none => 0 | some other => moments other r := by
    cases children state configuration child <;> simp [branchingChildMoment, Nat.ne_of_gt hr]
  unfold branchingMomentRemainder
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [hchild]
  rw [hlinear]
  ring

end
end Universality

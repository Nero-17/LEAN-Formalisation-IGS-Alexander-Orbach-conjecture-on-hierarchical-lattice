import Universality.Probability.BranchingMoments

namespace Universality
noncomputable section
set_option maxHeartbeats 0
variable {ι Ω J : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Ω] [DecidableEq Ω] [Fintype J] [DecidableEq J]

def branchingRemainderCoefficient (weight reward : ι → Ω → ℝ) (r : ℕ) (state : ι) : ℝ :=
  ∑ configuration, weight state configuration *
    ((∑ k ∈ Finset.range r, reward state configuration ^ (r - k) * (r.choose k : ℝ) *
      (Fintype.card J : ℝ) ^ k) +
      ((Finset.univ.filter fun assignment : Fin r → J => ¬ ∃ child, assignment = fun _ => child).card : ℝ))

theorem branchingMomentRemainder_bound
    (weight reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι)
    (hweight : ∀ state configuration, 0 ≤ weight state configuration)
    (hreward : ∀ state configuration, 0 ≤ reward state configuration)
    (moments : ι → ℕ → ℝ) (constant radius : ℝ)
    (hconstant : 1 ≤ constant) (hradius : 1 ≤ radius) (n r : ℕ)
    (hnonneg : ∀ state k, 0 ≤ moments state k)
    (hbound : ∀ state k, k < r → moments state k ≤ constant * radius ^ (k * n))
    (state : ι) :
    branchingMomentRemainder weight reward children moments r state ≤
      branchingRemainderCoefficient (J := J) weight reward r state *
        (constant ^ Fintype.card J * radius ^ (r * n)) := by
  have hproduct (configuration : Ω) (k : ℕ) (assignment : Fin k → J)
      (hk : k ≤ r) (hlower : ∀ child, Fintype.card {a : Fin k // assignment a = child} < r) :
      (∏ child, branchingChildMoment moments (children state configuration child)
        (Fintype.card {a : Fin k // assignment a = child})) ≤
        constant ^ Fintype.card J * radius ^ (r * n) := by
    apply (assignment_moment_product_bound
      (fun child => branchingChildMoment moments (children state configuration child)) constant radius
      (le_trans zero_le_one hconstant) (le_trans zero_le_one hradius) n k r assignment
      (fun child order => branchingChildMoment_nonneg moments hnonneg _ _)
      (fun child order horder => branchingChildMoment_bound moments constant radius hconstant hradius n r
        hbound _ order horder) hlower).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hradius (Nat.mul_le_mul_right n hk))
      (pow_nonneg (le_trans zero_le_one hconstant) _)
  have hassignment (configuration : Ω) (k : ℕ) (hk : k < r) :
      assignmentMomentSum (fun child => branchingChildMoment moments (children state configuration child)) k ≤
        (Fintype.card J : ℝ) ^ k * (constant ^ Fintype.card J * radius ^ (r * n)) := by
    unfold assignmentMomentSum
    calc
      _ ≤ ∑ _ : Fin k → J, constant ^ Fintype.card J * radius ^ (r * n) := by
        apply Finset.sum_le_sum
        intro assignment _
        apply hproduct configuration k assignment hk.le
        intro child
        exact lt_of_le_of_lt (by simpa only [Fintype.card_fin] using
          Fintype.card_subtype_le (fun a : Fin k => assignment a = child)) hk
      _ = _ := by simp [Fintype.card_fun]
  have hmixed (configuration : Ω) :
      (∑ assignment ∈ (Finset.univ.filter fun assignment : Fin r → J =>
        ¬ ∃ child, assignment = fun _ => child),
        ∏ child, branchingChildMoment moments (children state configuration child)
          (Fintype.card {a : Fin r // assignment a = child})) ≤
      ((Finset.univ.filter fun assignment : Fin r → J =>
        ¬ ∃ child, assignment = fun _ => child).card : ℝ) *
        (constant ^ Fintype.card J * radius ^ (r * n)) := by
    calc
      _ ≤ ∑ _assignment ∈ (Finset.univ.filter fun assignment : Fin r → J =>
          ¬ ∃ child, assignment = fun _ => child), constant ^ Fintype.card J * radius ^ (r * n) := by
        apply Finset.sum_le_sum
        intro assignment hassignment
        apply hproduct configuration r assignment le_rfl
        exact fiber_card_lt_of_nonconstant assignment (Finset.mem_filter.mp hassignment).2
      _ = _ := by simp [nsmul_eq_mul]
  unfold branchingMomentRemainder branchingRemainderCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro configuration _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hweight state configuration)
  rw [add_mul, Finset.sum_mul]
  apply add_le_add _ (hmixed configuration)
  apply Finset.sum_le_sum
  intro k hk
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (hassignment configuration k (Finset.mem_range.mp hk))
    (mul_nonneg (pow_nonneg (hreward state configuration) (r - k)) (Nat.cast_nonneg (r.choose k)))

end
end Universality

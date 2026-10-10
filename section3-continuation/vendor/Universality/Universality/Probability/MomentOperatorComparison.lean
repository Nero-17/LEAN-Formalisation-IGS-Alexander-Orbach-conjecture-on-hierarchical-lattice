import Universality.Probability.BranchingMoments

namespace Universality
noncomputable section
variable {ι Ω J : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Ω] [DecidableEq Ω] [Fintype J] [DecidableEq J]

theorem assignmentMomentSum_nonneg (moments : J → ℕ → ℝ)
    (hnonneg : ∀ child order, 0 ≤ moments child order) (order : ℕ) :
    0 ≤ assignmentMomentSum moments order := by
  exact Finset.sum_nonneg (fun assignment _ => Finset.prod_nonneg (fun child _ => hnonneg _ _))

theorem assignmentMomentSum_scale_comparison (first second : J → ℕ → ℝ)
    (hfirst : ∀ child order, 0 ≤ first child order)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hbound : ∀ child order, first child order ≤ scale ^ order * second child order)
    (order : ℕ) :
    assignmentMomentSum first order ≤ scale ^ order * assignmentMomentSum second order := by
  unfold assignmentMomentSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro assignment _
  calc
    _ ≤ ∏ child, scale ^ Fintype.card {a : Fin order // assignment a = child} *
        second child (Fintype.card {a : Fin order // assignment a = child}) := by
      apply Finset.prod_le_prod
      · intro child _
        exact hfirst _ _
      · intro child _
        exact hbound _ _
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_assignment_fiber_card]

theorem branchingChildMoment_scale_comparison (first second : ι → ℕ → ℝ)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hbound : ∀ state order, first state order ≤ scale ^ order * second state order)
    (child : Option ι) (order : ℕ) :
    branchingChildMoment first child order ≤ scale ^ order * branchingChildMoment second child order := by
  cases child with
  | none => by_cases hzero : order = 0 <;> simp [branchingChildMoment, hzero]
  | some state => exact hbound _ _

theorem branchingMomentOperator_nonneg (weight reward : ι → Ω → ℝ)
    (children : ι → Ω → J → Option ι) (moments : ι → ℕ → ℝ)
    (hweight : ∀ state configuration, 0 ≤ weight state configuration)
    (hreward : ∀ state configuration, 0 ≤ reward state configuration)
    (hmoments : ∀ state order, 0 ≤ moments state order) (order : ℕ) (state : ι) :
    0 ≤ branchingMomentOperator weight reward children moments order state := by
  apply Finset.sum_nonneg
  intro configuration _
  apply mul_nonneg (hweight _ _)
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (pow_nonneg (hreward _ _) _) (Nat.cast_nonneg _))
    (assignmentMomentSum_nonneg _ (fun child r => branchingChildMoment_nonneg moments hmoments _ r) _)

/-- Comparing each configuration weight costs one factor, while scaling
child moments costs the total degree of the corresponding monomial. -/
theorem branchingMomentOperator_scale_comparison
    (firstWeight secondWeight reward : ι → Ω → ℝ) (children : ι → Ω → J → Option ι)
    (firstMoments secondMoments : ι → ℕ → ℝ)
    (hfirstWeight : ∀ state configuration, 0 ≤ firstWeight state configuration)
    (hsecondWeight : ∀ state configuration, 0 ≤ secondWeight state configuration)
    (hreward : ∀ state configuration, 0 ≤ reward state configuration)
    (hfirstMoments : ∀ state order, 0 ≤ firstMoments state order)
    (hsecondMoments : ∀ state order, 0 ≤ secondMoments state order)
    (factor scale : ℝ) (hfactor : 1 ≤ factor) (hscale : 1 ≤ scale)
    (hweight : ∀ state configuration, firstWeight state configuration ≤ factor * secondWeight state configuration)
    (hmoments : ∀ state order, firstMoments state order ≤ scale ^ order * secondMoments state order)
    (order : ℕ) (horder : 1 ≤ order) (state : ι) :
    branchingMomentOperator firstWeight reward children firstMoments order state ≤
      (factor * scale) ^ order * branchingMomentOperator secondWeight reward children secondMoments order state := by
  have hscaleNonneg := zero_le_one.trans hscale
  have hfactorNonneg := zero_le_one.trans hfactor
  have hdegree (configuration : Ω) (k : ℕ) (hk : k ≤ order) :
      assignmentMomentSum (fun child => branchingChildMoment firstMoments (children state configuration child)) k ≤
        scale ^ order * assignmentMomentSum
          (fun child => branchingChildMoment secondMoments (children state configuration child)) k := by
    apply (assignmentMomentSum_scale_comparison _ _
      (fun child r => branchingChildMoment_nonneg firstMoments hfirstMoments _ r) scale hscaleNonneg
      (fun child r => branchingChildMoment_scale_comparison firstMoments secondMoments scale hscaleNonneg hmoments _ r) k).trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hscale hk)
      (assignmentMomentSum_nonneg _ (fun child r => branchingChildMoment_nonneg secondMoments hsecondMoments _ r) k)
  have hlinear : branchingMomentOperator firstWeight reward children firstMoments order state ≤
      factor * scale ^ order * branchingMomentOperator secondWeight reward children secondMoments order state := by
    unfold branchingMomentOperator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro configuration _
    have hsumNonneg : 0 ≤ ∑ k ∈ Finset.range (order + 1), reward state configuration ^ (order - k) *
        (order.choose k : ℝ) * assignmentMomentSum
          (fun child => branchingChildMoment secondMoments (children state configuration child)) k := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (mul_nonneg (pow_nonneg (hreward _ _) _) (Nat.cast_nonneg _))
        (assignmentMomentSum_nonneg _ (fun child r => branchingChildMoment_nonneg secondMoments hsecondMoments _ r) _)
    have hsum : (∑ k ∈ Finset.range (order + 1), reward state configuration ^ (order - k) *
        (order.choose k : ℝ) * assignmentMomentSum
          (fun child => branchingChildMoment firstMoments (children state configuration child)) k) ≤
        scale ^ order * ∑ k ∈ Finset.range (order + 1), reward state configuration ^ (order - k) *
          (order.choose k : ℝ) * assignmentMomentSum
            (fun child => branchingChildMoment secondMoments (children state configuration child)) k := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hb := mul_le_mul_of_nonneg_left (hdegree configuration k (by simpa using Finset.mem_range.mp hk))
        (mul_nonneg (pow_nonneg (hreward state configuration) (order - k)) (Nat.cast_nonneg (order.choose k)))
      convert hb using 1 <;> ring
    calc
      _ ≤ firstWeight state configuration * (scale ^ order * _) :=
        mul_le_mul_of_nonneg_left hsum (hfirstWeight _ _)
      _ ≤ (factor * secondWeight state configuration) * (scale ^ order * _) :=
        mul_le_mul_of_nonneg_right (hweight _ _) (mul_nonneg (pow_nonneg hscaleNonneg _) hsumNonneg)
      _ = _ := by ring
  apply hlinear.trans
  apply mul_le_mul_of_nonneg_right _
    (branchingMomentOperator_nonneg secondWeight reward children secondMoments hsecondWeight hreward hsecondMoments order state)
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ hfactor horder) (pow_nonneg hscaleNonneg _)

end
end Universality


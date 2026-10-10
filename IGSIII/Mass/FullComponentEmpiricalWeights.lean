import IGSIII.Mass.ComponentEmpiricalLaw
import IGSIII.Mass.ComponentMassGrowth

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section

open Universality Universality.FiniteNetwork MeasureTheory Filter
open scoped BigOperators Topology

/-- Every retained vertex is counted. The two persistent terminals and the
finite birth frontier are assigned to the chosen fallback component. -/
def fullComponentEmpiricalWordWeight (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool)) : ℝ :=
  (markedComponentVertexMass rule marks fine (List.ofFn word) +
    if word = fallback then componentFrontierVertexMass rule marks age [] + 2 else 0) /
      (markedComponentVertexMass rule marks (fine + age) [] + 2)

theorem fullComponentEmpiricalWordWeight_nonnegative (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool)) :
    0 ≤ fullComponentEmpiricalWordWeight rule marks fine age fallback word := by
  apply div_nonneg
  · apply add_nonneg (Nat.cast_nonneg _)
    split_ifs
    · exact add_nonneg (componentFrontierVertexMass_nonnegative rule marks age []) (by norm_num)
    · exact le_rfl
  · exact add_nonneg (Nat.cast_nonneg _) (by norm_num)

theorem fullComponentEmpiricalWordWeight_sum (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    ∑ word, fullComponentEmpiricalWordWeight rule marks fine age fallback word = 1 := by
  classical
  simp only [fullComponentEmpiricalWordWeight, ← Finset.sum_div, Finset.sum_add_distrib]
  have partition := actual_component_finite_partition rule marks crossing fine age []
  simp only [List.nil_append] at partition
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← add_assoc, add_comm (∑ word : Fin age → (Fin rule.edges × Bool), _) (componentFrontierVertexMass rule marks age []), ← partition]
  exact div_self (by linarith [show 0 ≤ markedComponentVertexMass rule marks (fine + age) [] from Nat.cast_nonneg _])

def fullComponentEmpiricalWordLaw (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool)) :
    Measure (Fin age → (Fin rule.edges × Bool)) :=
  (finiteWeightPMF (fullComponentEmpiricalWordWeight rule marks fine age fallback)
    (fullComponentEmpiricalWordWeight_nonnegative rule marks fine age fallback)
    (fullComponentEmpiricalWordWeight_sum rule marks crossing fine age fallback)).toMeasure

theorem ratio_add_constants_tendsto
    (numerator denominator : ℕ → ℝ) (limit extra added : ℝ)
    (growth : Tendsto denominator atTop atTop)
    (convergence : Tendsto (fun depth => numerator depth / denominator depth) atTop (𝓝 limit)) :
    Tendsto (fun depth => (numerator depth + extra) / (denominator depth + added)) atTop (𝓝 limit) := by
  have denominatorGrowth : Tendsto (fun depth => denominator depth + added) atTop atTop := by
    apply tendsto_atTop.mpr
    intro bound
    filter_upwards [growth.eventually (eventually_ge_atTop (bound - added))] with depth large
    linarith
  have inverse := tendsto_inv_atTop_zero.comp denominatorGrowth
  have factor : Tendsto (fun depth => denominator depth / (denominator depth + added)) atTop (𝓝 1) := by
    have result := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub
      (inverse.const_mul added)
    simp only [mul_zero, sub_zero] at result
    apply result.congr'
    filter_upwards [denominatorGrowth.eventually (eventually_gt_atTop (0 : ℝ))] with depth positive
    dsimp
    field_simp
    <;> ring
  have result := (convergence.mul factor).add (inverse.const_mul extra)
  simp only [mul_one, mul_zero, add_zero] at result
  apply result.congr'
  filter_upwards [growth.eventually (eventually_gt_atTop (0 : ℝ)),
    denominatorGrowth.eventually (eventually_gt_atTop (0 : ℝ))] with depth positive addedPositive
  dsimp
  field_simp
  <;> ring

theorem fullComponentEmpiricalWordWeight_tendsto (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (growth : Tendsto (fun depth => markedComponentVertexMass rule marks depth []) atTop atTop)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (age : ℕ) (fallback word : Fin age → (Fin rule.edges × Bool)) :
    Tendsto (fun fine => fullComponentEmpiricalWordWeight rule marks fine age fallback word)
      atTop (𝓝 (weight (List.ofFn word))) := by
  apply ratio_add_constants_tendsto
    (fun fine => markedComponentVertexMass rule marks fine (List.ofFn word))
    (fun fine => markedComponentVertexMass rule marks (fine + age) [])
    (weight (List.ofFn word)) (if word = fallback then componentFrontierVertexMass rule marks age [] + 2 else 0) 2
    (growth.comp (tendsto_add_atTop_nat age))
  simpa only [List.length_ofFn] using convergence (List.ofFn word)

end
end IGSIII.Chemical.Substitution

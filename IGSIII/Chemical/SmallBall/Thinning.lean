import Universality.Percolation.Bernoulli
import Mathlib.Tactic.Ring

/-!
# Independent thinning of an actual finite network

Each edge carries a pair of independent Bernoulli bits.  The first is the
original percolation bit and the second retains it.  We prove the product
parameter law by summing the genuine finite product weights, and then condition
on the original graph crossing.  No thinning identity is assumed.
-/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork
open scoped BigOperators

noncomputable section

variable {vertices edges : ℕ}

def bitWeight (parameter : ℝ) (bit : Bool) : ℝ :=
  if bit then parameter else 1 - parameter

def pairWeight (original retain : ℝ) (bits : Bool × Bool) : ℝ :=
  bitWeight original bits.1 * bitWeight retain bits.2

def pairedConfigurationWeight (original retain : ℝ)
    (sample : Fin edges → Bool × Bool) : ℝ :=
  ∏ edge, pairWeight original retain (sample edge)

def originalConfiguration (sample : Fin edges → Bool × Bool) : Configuration edges :=
  fun edge => (sample edge).1

def retentionConfiguration (sample : Fin edges → Bool × Bool) : Configuration edges :=
  fun edge => (sample edge).2

def thinnedConfiguration (sample : Fin edges → Bool × Bool) : Configuration edges :=
  fun edge => (sample edge).1 && (sample edge).2

theorem pairedConfigurationWeight_eq_product (original retain : ℝ)
    (sample : Fin edges → Bool × Bool) :
    pairedConfigurationWeight original retain sample =
      bernoulliWeight original (originalConfiguration sample) *
        bernoulliWeight retain (retentionConfiguration sample) := by
  unfold pairedConfigurationWeight pairWeight
  rw [Finset.prod_mul_distrib]
  rfl

theorem pairWeight_nonnegative {original retain : ℝ}
    (originalNonnegative : 0 ≤ original) (originalAtMostOne : original ≤ 1)
    (retainNonnegative : 0 ≤ retain) (retainAtMostOne : retain ≤ 1)
    (bits : Bool × Bool) : 0 ≤ pairWeight original retain bits := by
  apply mul_nonneg
  · cases bits.1 <;> simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
    · exact sub_nonneg.mpr originalAtMostOne
    · exact originalNonnegative
  · cases bits.2 <;> simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
    · exact sub_nonneg.mpr retainAtMostOne
    · exact retainNonnegative

theorem sum_pairWeight (original retain : ℝ) :
    ∑ bits : Bool × Bool, pairWeight original retain bits = 1 := by
  simp [Fintype.sum_prod_type, pairWeight, bitWeight]
  ring

theorem pairedConfigurationWeight_nonnegative {original retain : ℝ}
    (originalNonnegative : 0 ≤ original) (originalAtMostOne : original ≤ 1)
    (retainNonnegative : 0 ≤ retain) (retainAtMostOne : retain ≤ 1)
    (sample : Fin edges → Bool × Bool) :
    0 ≤ pairedConfigurationWeight original retain sample := by
  apply Finset.prod_nonneg
  intro edge _
  exact pairWeight_nonnegative originalNonnegative originalAtMostOne
    retainNonnegative retainAtMostOne (sample edge)

theorem sum_pairedConfigurationWeight (original retain : ℝ) :
    ∑ sample : Fin edges → Bool × Bool,
      pairedConfigurationWeight original retain sample = 1 := by
  unfold pairedConfigurationWeight
  rw [← Fintype.prod_sum]
  simp [sum_pairWeight]

theorem local_thinning_weight (original retain : ℝ) (opened : Bool) :
    (∑ bits : Bool × Bool,
      if (bits.1 && bits.2) = opened then pairWeight original retain bits else 0) =
      bitWeight (original * retain) opened := by
  cases opened <;> simp [Fintype.sum_prod_type, pairWeight, bitWeight] <;> ring

theorem local_original_weight (original retain : ℝ) (opened : Bool) :
    (∑ bits : Bool × Bool,
      if bits.1 = opened then pairWeight original retain bits else 0) =
      bitWeight original opened := by
  cases opened <;> simp [Fintype.sum_prod_type, pairWeight, bitWeight] <;> ring

theorem finite_product_bool_fiber {State : Type*} [Fintype State]
    (weight : State → ℝ) (transform : State → Bool) (parameter : ℝ)
    (localLaw : ∀ opened,
      (∑ state, if transform state = opened then weight state else 0) =
        bitWeight parameter opened)
    (configuration : Configuration edges) :
    (∑ sample : Fin edges → State,
      if (fun edge => transform (sample edge)) = configuration then
        ∏ edge, weight (sample edge) else 0) =
      bernoulliWeight parameter configuration := by
  classical
  have fiber : (∑ sample : Fin edges → State,
      if (fun edge => transform (sample edge)) = configuration then
        ∏ edge, weight (sample edge) else 0) =
      ∏ edge : Fin edges, ∑ state,
        if transform state = configuration edge then weight state else 0 := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro sample _
    by_cases equality : (fun edge => transform (sample edge)) = configuration
    · subst configuration
      simp
    · rw [if_neg equality]
      symm
      have witness : ∃ edge, transform (sample edge) ≠ configuration edge := by
        by_contra absent
        apply equality
        funext edge
        exact not_not.mp (fun different => absent ⟨edge, different⟩)
      obtain ⟨edge, different⟩ := witness
      apply Finset.prod_eq_zero (Finset.mem_univ edge)
      simp [different]
  rw [fiber]
  simp_rw [localLaw]
  rfl

theorem finite_product_bool_expectation {State : Type*} [Fintype State]
    (weight : State → ℝ) (transform : State → Bool) (parameter : ℝ)
    (localLaw : ∀ opened,
      (∑ state, if transform state = opened then weight state else 0) =
        bitWeight parameter opened)
    (response : Configuration edges → ℝ) :
    (∑ sample : Fin edges → State,
      (∏ edge, weight (sample edge)) * response (fun edge => transform (sample edge))) =
      ∑ configuration : Configuration edges,
        bernoulliWeight parameter configuration * response configuration := by
  classical
  have expansion (sample : Fin edges → State) :
      (∏ edge, weight (sample edge)) * response (fun edge => transform (sample edge)) =
        ∑ configuration : Configuration edges,
          (if (fun edge => transform (sample edge)) = configuration then
            ∏ edge, weight (sample edge) else 0) * response configuration := by
    simp [ite_mul]
  simp_rw [expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [← Finset.sum_mul, finite_product_bool_fiber weight transform parameter localLaw]

theorem thinned_crossing_weight (network : FiniteNetwork vertices edges)
    (original retain : ℝ) :
    (∑ sample : Fin edges → Bool × Bool,
      pairedConfigurationWeight original retain sample *
        (if network.crosses (thinnedConfiguration sample) then 1 else 0)) =
      network.reliability (original * retain) := by
  change (∑ sample : Fin edges → Bool × Bool,
    (∏ edge, pairWeight original retain (sample edge)) *
      (if network.crosses (fun edge => (sample edge).1 && (sample edge).2)
        then 1 else 0)) = _
  have equality := finite_product_bool_expectation (pairWeight original retain)
    (fun bits => bits.1 && bits.2) (original * retain)
    (local_thinning_weight original retain)
    (fun configuration => if network.crosses configuration then 1 else 0)
  simpa [pairedConfigurationWeight, thinnedConfiguration, reliability] using equality

theorem original_crossing_weight (network : FiniteNetwork vertices edges)
    (original retain : ℝ) :
    (∑ sample : Fin edges → Bool × Bool,
      pairedConfigurationWeight original retain sample *
        (if network.crosses (originalConfiguration sample) then 1 else 0)) =
      network.reliability original := by
  change (∑ sample : Fin edges → Bool × Bool,
    (∏ edge, pairWeight original retain (sample edge)) *
      (if network.crosses (fun edge => (sample edge).1) then 1 else 0)) = _
  have equality := finite_product_bool_expectation (pairWeight original retain)
    (fun bits => bits.1) original (local_original_weight original retain)
    (fun configuration => if network.crosses configuration then 1 else 0)
  simpa [pairedConfigurationWeight, originalConfiguration, reliability] using equality

theorem thinned_crosses_implies_original (network : FiniteNetwork vertices edges)
    (sample : Fin edges → Bool × Bool)
    (crossing : network.crosses (thinnedConfiguration sample) = true) :
    network.crosses (originalConfiguration sample) = true := by
  apply (network.crosses_eq_true _).mpr
  apply ((network.crosses_eq_true _).mp crossing).mono
  intro source target adjacency
  obtain ⟨distinct, edge, opened, endpoints⟩ := adjacency
  have both : (sample edge).1 = true ∧ (sample edge).2 = true := by
    simpa only [thinnedConfiguration, Bool.and_eq_true] using opened
  exact ⟨distinct, edge, both.1, endpoints⟩

/-- The displayed quotient is conditioning on the original crossing event;
`original_crossing_weight` identifies its actual normalizing weight. -/
theorem conditional_thinned_crossing_weight (network : FiniteNetwork vertices edges)
    (original retain : ℝ) :
    (∑ sample : Fin edges → Bool × Bool,
      if network.crosses (originalConfiguration sample) then
        pairedConfigurationWeight original retain sample *
          (if network.crosses (thinnedConfiguration sample) then 1 else 0)
      else 0) / network.reliability original =
      network.reliability (original * retain) / network.reliability original := by
  have collapse (sample : Fin edges → Bool × Bool) :
      (if network.crosses (originalConfiguration sample) then
        pairedConfigurationWeight original retain sample *
          (if network.crosses (thinnedConfiguration sample) then 1 else 0) else 0) =
      pairedConfigurationWeight original retain sample *
        (if network.crosses (thinnedConfiguration sample) then 1 else 0) := by
    by_cases crossing : network.crosses (thinnedConfiguration sample) = true
    · simp [crossing, thinned_crosses_implies_original network sample crossing]
    · simp [crossing]
  simp_rw [collapse]
  rw [thinned_crossing_weight]

theorem conditional_thinning_at_fixed_point (network : FiniteNetwork vertices edges)
    {critical : ℝ} (fixedPoint : network.reliability critical = critical) (retain : ℝ) :
    (∑ sample : Fin edges → Bool × Bool,
      if network.crosses (originalConfiguration sample) then
        pairedConfigurationWeight critical retain sample *
          (if network.crosses (thinnedConfiguration sample) then 1 else 0)
      else 0) / critical = network.reliability (critical * retain) / critical := by
  simpa only [fixedPoint] using
    conditional_thinned_crossing_weight network critical retain

end
end IGSIII.Chemical.SmallBall

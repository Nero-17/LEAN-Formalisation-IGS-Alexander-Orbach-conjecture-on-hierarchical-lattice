import Universality.Percolation.EdgeScoreIdentities
import Universality.Percolation.SimpleConfigurations
import Mathlib.Data.Fin.Tuple.Basic

namespace Universality.FiniteNetwork
noncomputable section

variable {edges : ℕ}

theorem expectation_const (p value : ℝ) :
    expectation (edges := edges) p (fun _ => value) = value := by
  simp only [expectation, ← Finset.sum_mul, sum_bernoulliWeight, one_mul]

theorem expectation_add (p : ℝ) (first second : Configuration edges → ℝ) :
    expectation p (fun ω => first ω + second ω) = expectation p first + expectation p second := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_mul_const (p value : ℝ) (response : Configuration edges → ℝ) :
    expectation p (fun ω => response ω * value) = expectation p response * value := by
  simp only [expectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_const_mul (p value : ℝ) (response : Configuration edges → ℝ) :
    expectation p (fun ω => value * response ω) = value * expectation p response := by
  simpa only [mul_comm] using expectation_mul_const p value response

def bernoulliVariance (p : ℝ) (response : Configuration edges → ℝ) : ℝ :=
  expectation p (fun ω => response ω ^ 2) - expectation p response ^ 2

theorem bernoulliVariance_eq_centered_square (p : ℝ) (response : Configuration edges → ℝ) :
    bernoulliVariance p response =
      expectation p (fun ω => (response ω - expectation p response) ^ 2) := by
  have hfun : (fun ω => (response ω - expectation p response) ^ 2) =
      fun ω => response ω ^ 2 - 2 * (response ω * expectation p response) +
        expectation p response ^ 2 := by funext ω; ring
  rw [hfun, expectation_add, expectation_sub, expectation_const_mul,
    expectation_mul_const, expectation_const]
  unfold bernoulliVariance
  ring

theorem bernoulliVariance_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (response : Configuration edges → ℝ) : 0 ≤ bernoulliVariance p response := by
  rw [bernoulliVariance_eq_centered_square]
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (bernoulliWeight_nonneg hp hp' ω) (sq_nonneg _)

theorem expectation_square_le {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (response : Configuration edges → ℝ) :
    expectation p response ^ 2 ≤ expectation p (fun ω => response ω ^ 2) :=
  sub_nonneg.mp (bernoulliVariance_nonneg hp hp' response)

def headConfigurationEquiv (edges : ℕ) :
    Configuration (edges + 1) ≃ Bool × Configuration edges where
  toFun ω := (ω 0, fun edge => ω edge.succ)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv ω := by funext edge; refine Fin.cases ?_ (fun i => ?_) edge <;> rfl
  right_inv pair := by cases pair; rfl

theorem bernoulliWeight_cons (p : ℝ) (opened : Bool) (ω : Configuration edges) :
    bernoulliWeight p (Fin.cons opened ω) =
      (if opened then p else 1 - p) * bernoulliWeight p ω := by
  simp only [bernoulliWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem expectation_cons (p : ℝ) (response : Configuration (edges + 1) → ℝ) :
    expectation p response =
      (1 - p) * expectation p (fun ω => response (Fin.cons false ω)) +
        p * expectation p (fun ω => response (Fin.cons true ω)) := by
  unfold expectation
  rw [← (headConfigurationEquiv edges).symm.sum_comp
    (fun ω => bernoulliWeight p ω * response ω), Fintype.sum_prod_type, Fintype.sum_bool]
  change (∑ ω : Configuration edges, bernoulliWeight p (Fin.cons true ω) * response (Fin.cons true ω)) +
    (∑ ω : Configuration edges, bernoulliWeight p (Fin.cons false ω) * response (Fin.cons false ω)) = _
  simp only [bernoulliWeight_cons, Bool.false_eq_true, ↓reduceIte,
    mul_assoc, ← Finset.mul_sum]
  exact add_comm _ _

theorem variance_cons (p : ℝ) (response : Configuration (edges + 1) → ℝ) :
    bernoulliVariance p response =
      (1 - p) * bernoulliVariance p (fun ω => response (Fin.cons false ω)) +
      p * bernoulliVariance p (fun ω => response (Fin.cons true ω)) +
      p * (1 - p) * (expectation p (fun ω => response (Fin.cons true ω)) -
        expectation p (fun ω => response (Fin.cons false ω))) ^ 2 := by
  simp only [bernoulliVariance, expectation_cons]
  ring

def bernoulliEnergy (p : ℝ) (response : Configuration edges → ℝ) : ℝ :=
  ∑ edge : Fin edges, expectation p (fun ω =>
    (response (Function.update ω edge true) - response (Function.update ω edge false)) ^ 2)

theorem energy_cons (p : ℝ) (response : Configuration (edges + 1) → ℝ) :
    bernoulliEnergy p response =
      expectation p (fun ω => (response (Fin.cons true ω) - response (Fin.cons false ω)) ^ 2) +
      (1 - p) * bernoulliEnergy p (fun ω => response (Fin.cons false ω)) +
      p * bernoulliEnergy p (fun ω => response (Fin.cons true ω)) := by
  unfold bernoulliEnergy
  rw [Fin.sum_univ_succ]
  simp only [expectation_cons, Fin.update_cons_zero, ← Fin.cons_update]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem bernoulli_poincare {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (response : Configuration edges → ℝ) :
    bernoulliVariance p response ≤ p * (1 - p) * bernoulliEnergy p response := by
  induction edges with
  | zero => simp [bernoulliVariance, bernoulliEnergy, expectation, bernoulliWeight]
  | succ edges ih =>
    have hfalse := mul_le_mul_of_nonneg_left (ih (fun ω => response (Fin.cons false ω)))
      (sub_nonneg.mpr hp')
    have htrue := mul_le_mul_of_nonneg_left (ih (fun ω => response (Fin.cons true ω))) hp
    have hsquare := mul_le_mul_of_nonneg_left
      (expectation_square_le hp hp'
        (fun ω => response (Fin.cons true ω) - response (Fin.cons false ω)))
      (mul_nonneg hp (sub_nonneg.mpr hp'))
    rw [expectation_sub] at hsquare
    rw [variance_cons, energy_cons]
    nlinarith

theorem bernoulliVariance_pos_of_ne {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (response : Configuration edges → ℝ) (first second : Configuration edges)
    (hne : response first ≠ response second) : 0 < bernoulliVariance p response := by
  rw [bernoulliVariance_eq_centered_square]
  apply (Finset.sum_pos_iff_of_nonneg (fun ω _ =>
    mul_nonneg (bernoulliWeight_pos hp hp' ω).le (sq_nonneg _))).mpr
  have hexists : ∃ ω, response ω ≠ expectation p response := by
    by_cases h : response first = expectation p response
    · refine ⟨second, ?_⟩
      intro hs
      exact hne (h.trans hs.symm)
    · exact ⟨first, h⟩
  obtain ⟨ω, hω⟩ := hexists
  exact ⟨ω, Finset.mem_univ _, mul_pos (bernoulliWeight_pos hp hp' ω)
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hω))⟩

theorem variance_le_energy_sub_head_variance {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (response : Configuration (edges + 1) → ℝ) :
    bernoulliVariance p response ≤ p * (1 - p) *
      (bernoulliEnergy p response - bernoulliVariance p
        (fun ω => response (Fin.cons true ω) - response (Fin.cons false ω))) := by
  have hfalse := mul_le_mul_of_nonneg_left
    (bernoulli_poincare hp hp' (fun ω => response (Fin.cons false ω))) (sub_nonneg.mpr hp')
  have htrue := mul_le_mul_of_nonneg_left
    (bernoulli_poincare hp hp' (fun ω => response (Fin.cons true ω))) hp
  have hhead : bernoulliVariance p
      (fun ω => response (Fin.cons true ω) - response (Fin.cons false ω)) =
      expectation p (fun ω => (response (Fin.cons true ω) - response (Fin.cons false ω)) ^ 2) -
      (expectation p (fun ω => response (Fin.cons true ω)) -
        expectation p (fun ω => response (Fin.cons false ω))) ^ 2 := by
    rw [bernoulliVariance, expectation_sub]
  rw [variance_cons, energy_cons, hhead]
  nlinarith

theorem cons_false_closed : Fin.cons false (fun _ : Fin edges => false) = (fun _ => false) := by
  funext edge
  refine Fin.cases ?_ (fun i => ?_) edge <;> rfl

theorem cons_true_open : Fin.cons true (fun _ : Fin edges => true) = (fun _ => true) := by
  funext edge
  refine Fin.cases ?_ (fun i => ?_) edge <;> rfl

theorem cons_true_closed : Fin.cons true (fun _ : Fin edges => false) = onlyOpen 0 := by
  rw [← Fin.update_cons_zero (x := false), cons_false_closed]
  rfl

theorem cons_false_onlyOpen (edge : Fin edges) :
    Fin.cons false (onlyOpen edge) = onlyOpen edge.succ := by
  simp only [onlyOpen, Fin.cons_update, cons_false_closed]

/-- Strict product-space Poincare inequality for an observable that vanishes
on the empty and every singleton configuration but is one on the full set.
This excludes all affine functions, without assuming Boolean monotonicity. -/
theorem strict_bernoulli_poincare {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (response : Configuration edges → ℝ)
    (hzero : response (fun _ => false) = 0)
    (hsingle : ∀ edge, response (onlyOpen edge) = 0)
    (hall : response (fun _ => true) = 1) :
    bernoulliVariance p response < p * (1 - p) * bernoulliEnergy p response := by
  induction edges with
  | zero =>
    have hconfig : (fun _ : Fin 0 => false) = (fun _ => true) := by funext e; exact e.elim0
    rw [hconfig, hall] at hzero
    norm_num at hzero
  | succ edges ih =>
    by_cases h : ∃ ω : Configuration edges, response (Fin.cons true ω) ≠ response (Fin.cons false ω)
    · obtain ⟨ω, hω⟩ := h
      have hheadzero : response (Fin.cons true (fun _ : Fin edges => false)) -
          response (Fin.cons false (fun _ : Fin edges => false)) = 0 := by
        rw [cons_true_closed, cons_false_closed, hsingle, hzero, sub_self]
      have hvar := bernoulliVariance_pos_of_ne hp hp'
        (fun η => response (Fin.cons true η) - response (Fin.cons false η))
        ω (fun _ => false) (by rw [hheadzero]; exact sub_ne_zero.mpr hω)
      have hbound := variance_le_energy_sub_head_variance hp.le hp'.le response
      have hpositive := mul_pos (mul_pos hp (sub_pos.mpr hp')) hvar
      nlinarith
    · push Not at h
      have hz : (fun ω : Configuration edges => response (Fin.cons false ω)) (fun _ => false) = 0 := by
        simpa only [cons_false_closed] using hzero
      have hs : ∀ edge : Fin edges, response (Fin.cons false (onlyOpen edge)) = 0 := by
        intro edge
        rw [cons_false_onlyOpen, hsingle]
      have ha : response (Fin.cons false (fun _ : Fin edges => true)) = 1 := by
        rw [← h, cons_true_open, hall]
      have hresult := ih (fun ω => response (Fin.cons false ω)) hz hs ha
      have hvariance : bernoulliVariance p response =
          bernoulliVariance p (fun ω => response (Fin.cons false ω)) := by
        rw [variance_cons]
        simp_rw [h]
        ring
      have henergy : bernoulliEnergy p response =
          bernoulliEnergy p (fun ω => response (Fin.cons false ω)) := by
        rw [energy_cons]
        simp_rw [h, sub_self, zero_pow (by decide : 2 ≠ 0)]
        rw [expectation_const]
        ring
      rw [hvariance, henergy]
      exact hresult

end
end Universality.FiniteNetwork

import Universality.Percolation.Bernoulli
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace Universality.FiniteNetwork
noncomputable section

variable {edges : ℕ}

def RemainingConfiguration (edge : Fin edges) := {other : Fin edges // other ≠ edge} → Bool

instance (edge : Fin edges) : Fintype (RemainingConfiguration edge) := by
  unfold RemainingConfiguration
  infer_instance

def insertEdge (edge : Fin edges) (opened : Bool) (rest : RemainingConfiguration edge) :
    Configuration edges := fun other => if h : other = edge then opened else rest ⟨other, h⟩

def splitConfiguration (edge : Fin edges) :
    Configuration edges ≃ Bool × RemainingConfiguration edge where
  toFun ω := (ω edge, fun other => ω other.val)
  invFun pair := insertEdge edge pair.1 pair.2
  left_inv ω := by
    funext other
    simp only [insertEdge]
    split <;> simp_all
  right_inv pair := by
    apply Prod.ext
    · simp [insertEdge]
    · funext other
      simp [insertEdge, other.property]

theorem insertEdge_self (edge : Fin edges) (opened : Bool) (rest : RemainingConfiguration edge) :
    insertEdge edge opened rest edge = opened := by simp [insertEdge]

theorem insertEdge_other (edge : Fin edges) (opened : Bool) (rest : RemainingConfiguration edge)
    (other : Fin edges) (hne : other ≠ edge) :
    insertEdge edge opened rest other = rest ⟨other, hne⟩ := by simp [insertEdge, hne]

def erasedWeight (p : ℝ) (ω : Configuration edges) (edge : Fin edges) : ℝ :=
  ∏ other ∈ Finset.univ.erase edge, if ω other then p else 1 - p

theorem erasedWeight_insertEdge (p : ℝ) (edge : Fin edges)
    (opened : Bool) (rest : RemainingConfiguration edge) :
    erasedWeight p (insertEdge edge opened rest) edge =
      erasedWeight p (insertEdge edge false rest) edge := by
  apply Finset.prod_congr rfl
  intro other hother
  rw [insertEdge_other edge opened rest other (Finset.ne_of_mem_erase hother),
    insertEdge_other edge false rest other (Finset.ne_of_mem_erase hother)]

theorem bernoulliWeight_insertEdge (p : ℝ) (edge : Fin edges)
    (opened : Bool) (rest : RemainingConfiguration edge) :
    bernoulliWeight p (insertEdge edge opened rest) =
      erasedWeight p (insertEdge edge false rest) edge * (if opened then p else 1 - p) := by
  unfold bernoulliWeight
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ edge), insertEdge_self]
  rw [← erasedWeight, erasedWeight_insertEdge]

theorem sum_splitConfiguration {α : Type*} [AddCommMonoid α]
    (edge : Fin edges) (response : Configuration edges → α) :
    (∑ ω, response ω) =
      ∑ rest : RemainingConfiguration edge,
        (response (insertEdge edge false rest) + response (insertEdge edge true rest)) := by
  classical
  rw [← (splitConfiguration edge).symm.sum_comp response]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Equiv.symm_apply_apply, splitConfiguration]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rest _
  exact add_comm _ _

theorem hasDerivAt_bernoulliWeight (ω : Configuration edges) (p : ℝ) :
    HasDerivAt (fun p => bernoulliWeight p ω)
      (∑ edge : Fin edges, erasedWeight p ω edge * (if ω edge then 1 else -1)) p := by
  have derivative (edge : Fin edges) :
      HasDerivAt (fun p : ℝ => if ω edge then p else 1 - p)
        (if ω edge then 1 else -1) p := by
    cases ω edge
    · exact (hasDerivAt_id p).const_sub 1
    · exact hasDerivAt_id p
  simpa only [bernoulliWeight, erasedWeight, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (u := Finset.univ) (fun edge _ => derivative edge)

def expectation (p : ℝ) (response : Configuration edges → ℝ) : ℝ :=
  ∑ ω, bernoulliWeight p ω * response ω

theorem hasDerivAt_expectation (response : Configuration edges → ℝ) (p : ℝ) :
    HasDerivAt (fun p => expectation p response)
      (∑ ω : Configuration edges,
        (∑ edge : Fin edges, erasedWeight p ω edge * (if ω edge then 1 else -1)) * response ω) p := by
  unfold expectation
  exact HasDerivAt.fun_sum (fun ω _ => (hasDerivAt_bernoulliWeight ω p).mul_const (response ω))

theorem update_insertEdge (edge : Fin edges) (opened replacement : Bool)
    (rest : RemainingConfiguration edge) :
    Function.update (insertEdge edge opened rest) edge replacement = insertEdge edge replacement rest := by
  funext other
  by_cases h : other = edge
  · subst other
    simp [insertEdge]
  · simp [Function.update_of_ne h, insertEdge, h]

theorem derivative_edge_eq_resampling (response : Configuration edges → ℝ)
    (p : ℝ) (edge : Fin edges) :
    (∑ ω : Configuration edges,
      erasedWeight p ω edge * (if ω edge then 1 else -1) * response ω) =
      expectation p (fun ω => response (Function.update ω edge true) -
        response (Function.update ω edge false)) := by
  unfold expectation
  rw [sum_splitConfiguration edge, sum_splitConfiguration edge]
  apply Finset.sum_congr rfl
  intro rest _
  simp only [erasedWeight_insertEdge, insertEdge_self, update_insertEdge,
    bernoulliWeight_insertEdge, Bool.false_eq_true, ↓reduceIte]
  ring

theorem hasDerivAt_expectation_resampling (response : Configuration edges → ℝ) (p : ℝ) :
    HasDerivAt (fun p => expectation p response)
      (∑ edge : Fin edges, expectation p (fun ω => response (Function.update ω edge true) -
        response (Function.update ω edge false))) p := by
  have h := hasDerivAt_expectation response p
  simp_rw [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  simp_rw [derivative_edge_eq_resampling] at h
  exact h

theorem expectation_open_independent (response : Configuration edges → ℝ)
    (p : ℝ) (edge : Fin edges)
    (hindependent : ∀ ω opened, response (Function.update ω edge opened) = response ω) :
    expectation p (fun ω => if ω edge then response ω else 0) = p * expectation p response := by
  unfold expectation
  rw [sum_splitConfiguration edge, sum_splitConfiguration edge, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  have hresponse : response (insertEdge edge true rest) = response (insertEdge edge false rest) := by
    simpa only [update_insertEdge] using hindependent (insertEdge edge false rest) true
  simp only [bernoulliWeight_insertEdge, insertEdge_self, Bool.false_eq_true, ↓reduceIte, hresponse]
  ring

theorem expectation_closed_independent (response : Configuration edges → ℝ)
    (p : ℝ) (edge : Fin edges)
    (hindependent : ∀ ω opened, response (Function.update ω edge opened) = response ω) :
    expectation p (fun ω => if ω edge then 0 else response ω) = (1 - p) * expectation p response := by
  unfold expectation
  rw [sum_splitConfiguration edge, sum_splitConfiguration edge, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  have hresponse : response (insertEdge edge true rest) = response (insertEdge edge false rest) := by
    simpa only [update_insertEdge] using hindependent (insertEdge edge false rest) true
  simp only [bernoulliWeight_insertEdge, insertEdge_self, Bool.false_eq_true, ↓reduceIte, hresponse]
  ring

end
end Universality.FiniteNetwork

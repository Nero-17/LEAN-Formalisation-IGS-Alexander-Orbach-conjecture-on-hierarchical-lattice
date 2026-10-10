import Universality.Percolation.Bernoulli
import Universality.Matrix.PopulationGrowth

/-!
# First moments of the conditional offspring recursion

The one-generation response is defined from actual conditional Bernoulli
configurations and live child edges.  Matrix powers are proved to represent
the recursively iterated response.  Identification with clusters on a glued
hierarchical graph is a separate graph-substitution theorem.
-/

namespace Universality.FiniteNetwork
noncomputable section
open Matrix Filter
open scoped Topology

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def liveResponse (σ : LiveState) (ω : Configuration edges) (values : LiveState → ℝ) : ℝ :=
  ∑ e : Fin edges, match R.childState σ ω e with
    | none => 0
    | some τ => values τ

theorem liveResponse_eq (σ : LiveState) (ω : Configuration edges) (values : LiveState → ℝ) :
    R.liveResponse σ ω values = ∑ τ, (R.liveCount σ τ ω : ℝ) * values τ := by
  symm
  simp only [liveCount, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold liveResponse
  apply Finset.sum_congr rfl
  intro e _
  cases h : R.childState σ ω e with
  | none => simp
  | some τ => simp

def conditionalResponse (p : ℝ) (σ : LiveState) (values : LiveState → ℝ) : ℝ :=
  (∑ ω : Configuration edges,
    if R.conditioning σ ω then bernoulliWeight p ω * R.liveResponse σ ω values else 0) /
    R.conditioningProbability p σ

theorem massMatrix_mulVec_response (p : ℝ) (values : LiveState → ℝ) (σ : LiveState) :
    (R.massMatrix p *ᵥ values) σ = R.conditionalResponse p σ values := by
  simp only [Matrix.mulVec, dotProduct, massMatrix, conditionalResponse,
    div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with h
  · simp only [R.liveResponse_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    ring
  · simp

def generationResponse (p : ℝ) : ℕ → LiveState → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun σ => R.conditionalResponse p σ (generationResponse p n)

theorem generationResponse_eq_matrix_power (p : ℝ) (n : ℕ) :
    R.generationResponse p n = R.massMatrix p ^ n *ᵥ (fun _ => 1) := by
  induction n with
  | zero => simp [generationResponse]
  | succ n ih =>
      ext σ
      change R.conditionalResponse p σ (R.generationResponse p n) = _
      rw [← massMatrix_mulVec_response, ih,
        Matrix.mulVec_mulVec, ← pow_succ']

theorem conditioningProbability_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (σ : LiveState) : 0 ≤ R.conditioningProbability p σ := by
  apply Finset.sum_nonneg
  intro ω _
  split
  · exact bernoulliWeight_nonneg hp hp' ω
  · exact le_rfl

theorem massMatrix_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (σ τ : LiveState) : 0 ≤ R.massMatrix p σ τ := by
  apply div_nonneg _ (R.conditioningProbability_nonneg hp hp' σ)
  apply Finset.sum_nonneg
  intro ω _
  split
  · exact mul_nonneg (bernoulliWeight_nonneg hp hp' ω) (Nat.cast_nonneg _)
  · exact le_rfl

theorem generationResponse_dimension {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (weight : LiveState → ℝ) (radius scale : ℝ)
    (hw : ∀ σ, 0 < weight σ) (hr : 0 < radius)
    (heigen : R.massMatrix p *ᵥ weight = radius • weight) (σ : LiveState) :
    Tendsto (fun n : ℕ => Real.log (R.generationResponse p n σ) / Real.log (scale ^ n))
      atTop (𝓝 (Real.log radius / Real.log scale)) := by
  simpa only [generationResponse_eq_matrix_power, Matrix.mulVec, dotProduct, mul_one] using
    matrix_row_sum_dimension (R.massMatrix p) weight radius scale
      (R.massMatrix_nonneg hp hp') hw hr heigen σ

end
end Universality.FiniteNetwork

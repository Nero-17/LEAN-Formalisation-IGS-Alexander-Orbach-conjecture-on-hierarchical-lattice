import IGSIII34.Diffusion.FiniteResolventVariationalCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

def finiteDegreeNatCompletion (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) : ℕ :=
  ∑ edge, ((if (endpoint edge).1 = vertex then 1 else 0) + (if (endpoint edge).2 = vertex then 1 else 0))

theorem finiteDegreeNat_cast_completion (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    (finiteDegreeNatCompletion endpoint vertex : ℝ) = degree endpoint vertex := by
  simp [finiteDegreeNatCompletion, degree]

theorem finiteDegreeNat_le_completion (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    finiteDegreeNatCompletion endpoint vertex ≤ 2 * Fintype.card Edge := by
  calc
    _ ≤ ∑ _edge : Edge, 2 := by
      apply Finset.sum_le_sum
      intro edge member
      split_ifs <;> omega
    _ = _ := by simp [mul_comm]

def FiniteRegularizedEdgeCompletion (endpoint : Edge → Vertex × Vertex) :=
  (Edge × Bool) ⊕ (Σ vertex : Vertex, Fin (2 * Fintype.card Edge - finiteDegreeNatCompletion endpoint vertex))

instance finiteRegularizedEdgeFintypeCompletion (endpoint : Edge → Vertex × Vertex) :
    Fintype (FiniteRegularizedEdgeCompletion endpoint) := inferInstanceAs (Fintype (_ ⊕ _))

instance finiteRegularizedEdgeNonemptyCompletion [Nonempty Edge] (endpoint : Edge → Vertex × Vertex) :
    Nonempty (FiniteRegularizedEdgeCompletion endpoint) := ⟨Sum.inl (Classical.arbitrary Edge, true)⟩

def finiteRegularizedEndpointCompletion (endpoint : Edge → Vertex × Vertex) :
    FiniteRegularizedEdgeCompletion endpoint → Vertex × Vertex
  | Sum.inl edge => endpoint edge.1
  | Sum.inr loop => (loop.1, loop.1)

theorem finiteRegularized_degree_completion (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    degree (finiteRegularizedEndpointCompletion endpoint) vertex = 4 * (Fintype.card Edge : ℝ) := by
  classical
  unfold degree
  simp only [FiniteRegularizedEdgeCompletion, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion, Fintype.sum_sigma]
  have old : (∑ edge, ((if (endpoint edge).1 = vertex then (1 : ℝ) else 0) +
      (if (endpoint edge).2 = vertex then 1 else 0) + ((if (endpoint edge).1 = vertex then 1 else 0) +
        (if (endpoint edge).2 = vertex then 1 else 0)))) = 2 * degree endpoint vertex := by
    unfold degree
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge member
    ring
  have loops : (∑ point : Vertex, ∑ _index : Fin (2 * Fintype.card Edge - finiteDegreeNatCompletion endpoint point),
      ((if point = vertex then (1 : ℝ) else 0) + (if point = vertex then 1 else 0))) =
      2 * ((2 * Fintype.card Edge - finiteDegreeNatCompletion endpoint vertex : ℕ) : ℝ) := by
    simp [Finset.sum_add_distrib, mul_two, two_mul]
  rw [old, loops]
  rw [Nat.cast_sub (finiteDegreeNat_le_completion endpoint vertex), Nat.cast_mul,
    Nat.cast_ofNat, finiteDegreeNat_cast_completion]
  ring

theorem finiteRegularized_laplacian_completion (endpoint : Edge → Vertex × Vertex)
    (potential : Vertex → ℝ) (vertex : Vertex) :
    laplacian (finiteRegularizedEndpointCompletion endpoint) potential vertex =
      2 * laplacian endpoint potential vertex := by
  classical
  unfold laplacian
  simp only [FiniteRegularizedEdgeCompletion, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion, Fintype.sum_sigma]
  have loopZero (point : Vertex) :
      (if point = vertex then potential point - potential vertex else 0) = 0 := by
    split_ifs with equality
    · simp [equality]
    · rfl
  simp only [loopZero, add_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge member
  ring

theorem finiteRegularized_energy_completion (endpoint : Edge → Vertex × Vertex)
    (potential : Vertex → ℝ) :
    energy (finiteRegularizedEndpointCompletion endpoint) potential = 2 * energy endpoint potential := by
  classical
  unfold energy
  simp only [FiniteRegularizedEdgeCompletion, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion, Fintype.sum_sigma, sub_self,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge member
  ring

theorem finiteRegularized_mixed_energy_completion (endpoint : Edge → Vertex × Vertex)
    (potential test : Vertex → ℝ) :
    finiteMixedEnergyCompletion (finiteRegularizedEndpointCompletion endpoint) potential test =
      2 * finiteMixedEnergyCompletion endpoint potential test := by
  classical
  unfold finiteMixedEnergyCompletion
  simp only [FiniteRegularizedEdgeCompletion, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion, Fintype.sum_sigma, sub_self,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge member
  ring

end
end IGSIII34.Diffusion


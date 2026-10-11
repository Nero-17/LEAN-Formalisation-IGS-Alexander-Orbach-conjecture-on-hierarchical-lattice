import IGSIII34.Diffusion.FiniteResolventVariationalCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

def finiteDegreeNatCompletion20261011 (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) : ℕ :=
  ∑ edge, ((if (endpoint edge).1 = vertex then 1 else 0) + (if (endpoint edge).2 = vertex then 1 else 0))

theorem finiteDegreeNat_cast_completion20261011 (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    (finiteDegreeNatCompletion20261011 endpoint vertex : ℝ) = degree endpoint vertex := by
  simp [finiteDegreeNatCompletion20261011, degree]

theorem finiteDegreeNat_le_completion20261011 (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    finiteDegreeNatCompletion20261011 endpoint vertex ≤ 2 * Fintype.card Edge := by
  calc
    _ ≤ ∑ _edge : Edge, 2 := by
      apply Finset.sum_le_sum
      intro edge member
      split_ifs <;> omega
    _ = _ := by simp [mul_comm]

def FiniteRegularizedEdgeCompletion20261011 (endpoint : Edge → Vertex × Vertex) :=
  (Edge × Bool) ⊕ (Σ vertex : Vertex, Fin (2 * Fintype.card Edge - finiteDegreeNatCompletion20261011 endpoint vertex))

instance finiteRegularizedEdgeFintypeCompletion20261011 (endpoint : Edge → Vertex × Vertex) :
    Fintype (FiniteRegularizedEdgeCompletion20261011 endpoint) := inferInstanceAs (Fintype (_ ⊕ _))

instance finiteRegularizedEdgeNonemptyCompletion20261011 [Nonempty Edge] (endpoint : Edge → Vertex × Vertex) :
    Nonempty (FiniteRegularizedEdgeCompletion20261011 endpoint) := ⟨Sum.inl (Classical.arbitrary Edge, true)⟩

def finiteRegularizedEndpointCompletion20261011 (endpoint : Edge → Vertex × Vertex) :
    FiniteRegularizedEdgeCompletion20261011 endpoint → Vertex × Vertex
  | Sum.inl edge => endpoint edge.1
  | Sum.inr loop => (loop.1, loop.1)

theorem finiteRegularized_degree_completion20261011 (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    degree (finiteRegularizedEndpointCompletion20261011 endpoint) vertex = 4 * (Fintype.card Edge : ℝ) := by
  classical
  unfold degree
  simp only [FiniteRegularizedEdgeCompletion20261011, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion20261011, Fintype.sum_sigma]
  have old : (∑ edge, ((if (endpoint edge).1 = vertex then (1 : ℝ) else 0) +
      (if (endpoint edge).2 = vertex then 1 else 0) + ((if (endpoint edge).1 = vertex then 1 else 0) +
        (if (endpoint edge).2 = vertex then 1 else 0)))) = 2 * degree endpoint vertex := by
    unfold degree
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge member
    ring
  have loops : (∑ point : Vertex, ∑ _index : Fin (2 * Fintype.card Edge - finiteDegreeNatCompletion20261011 endpoint point),
      ((if point = vertex then (1 : ℝ) else 0) + (if point = vertex then 1 else 0))) =
      2 * ((2 * Fintype.card Edge - finiteDegreeNatCompletion20261011 endpoint vertex : ℕ) : ℝ) := by
    simp [Finset.sum_add_distrib, mul_two, two_mul]
  rw [old, loops]
  rw [Nat.cast_sub (finiteDegreeNat_le_completion20261011 endpoint vertex), Nat.cast_mul,
    Nat.cast_ofNat, finiteDegreeNat_cast_completion20261011]
  ring

theorem finiteRegularized_laplacian_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (potential : Vertex → ℝ) (vertex : Vertex) :
    laplacian (finiteRegularizedEndpointCompletion20261011 endpoint) potential vertex =
      2 * laplacian endpoint potential vertex := by
  classical
  unfold laplacian
  simp only [FiniteRegularizedEdgeCompletion20261011, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion20261011, Fintype.sum_sigma]
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

theorem finiteRegularized_energy_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (potential : Vertex → ℝ) :
    energy (finiteRegularizedEndpointCompletion20261011 endpoint) potential = 2 * energy endpoint potential := by
  classical
  unfold energy
  simp only [FiniteRegularizedEdgeCompletion20261011, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion20261011, Fintype.sum_sigma, sub_self,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge member
  ring

theorem finiteRegularized_mixed_energy_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (potential test : Vertex → ℝ) :
    finiteMixedEnergyCompletion20261011 (finiteRegularizedEndpointCompletion20261011 endpoint) potential test =
      2 * finiteMixedEnergyCompletion20261011 endpoint potential test := by
  classical
  unfold finiteMixedEnergyCompletion20261011
  simp only [FiniteRegularizedEdgeCompletion20261011, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, finiteRegularizedEndpointCompletion20261011, Fintype.sum_sigma, sub_self,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge member
  ring

end
end IGSIII34.Diffusion


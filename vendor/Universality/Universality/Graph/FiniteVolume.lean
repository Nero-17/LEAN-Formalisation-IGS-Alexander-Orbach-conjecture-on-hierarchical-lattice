import Universality.Percolation.InternalVertexMass
import Mathlib.Algebra.Ring.GeomSum

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem card_terminal_vertices : Fintype.card {v : Fin vertices // v = R.source ∨ v = R.target} = 2 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun v : Fin vertices => v = R.source ∨ v = R.target) =
      {R.source, R.target} := by ext v; simp
  rw [hset]
  simp [R.terminals_distinct]

include R in
theorem two_le_vertices : 2 ≤ vertices := by
  have h := Fintype.card_subtype_le (fun v : Fin vertices => v = R.source ∨ v = R.target)
  simpa only [R.card_terminal_vertices, Fintype.card_fin] using h

theorem card_interior_vertices : Fintype.card R.InteriorVertex = vertices - 2 := by
  calc
    _ = Fintype.card {v : Fin vertices // ¬ (v = R.source ∨ v = R.target)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => not_or.symm))
    _ = _ := by rw [Fintype.card_subtype_compl, Fintype.card_fin, R.card_terminal_vertices]

theorem card_substitution_vertices {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges) :
    Fintype.card (outer.SubstitutionVertex inner) = outerVertices + outerEdges * (innerVertices - 2) := by
  calc
    _ = Fintype.card (Fin outerVertices ⊕ (Fin outerEdges × inner.InteriorVertex)) :=
      Fintype.card_congr (Equiv.refl _)
    _ = _ := by rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, inner.card_interior_vertices]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem mul_vertices (outer inner : Rule) :
    (outer * inner).vertices = outer.vertices + outer.edges * (inner.vertices - 2) :=
  outer.network.card_substitution_vertices inner.network

/-- Exact finite-volume normalisation, including the two persistent terminals. -/
theorem generation_vertices (rule : Rule) (n : ℕ) :
    (rule.generation n).vertices =
      2 + (rule.vertices - 2) * ∑ k ∈ Finset.range (n + 1), rule.edges ^ k := by
  induction n with
  | zero =>
    have hvertices := rule.network.two_le_vertices
    simp only [generation, zero_add, Finset.sum_range_one, pow_zero, mul_one]
    omega
  | succ n ih =>
    conv_rhs => rw [Finset.sum_range_succ]
    rw [generation, mul_vertices, ih, generation_edges]
    ring

theorem generation_volume_formula (rule : Rule) (n : ℕ) (hedges : rule.edges ≠ 1) :
    ((rule.generation n).vertices : ℝ) =
      2 + ((rule.vertices : ℝ) - 2) * ((rule.edges : ℝ) ^ (n + 1) - 1) /
        ((rule.edges : ℝ) - 1) := by
  have hvertices := rule.network.two_le_vertices
  rw [generation_vertices]
  push_cast [Nat.cast_sub hvertices]
  have hne : (rule.edges : ℝ) - 1 ≠ 0 := by
    intro h
    apply hedges
    exact_mod_cast (sub_eq_zero.mp h)
  have hsum : (∑ k ∈ Finset.range (n + 1), (rule.edges : ℝ) ^ k) =
      ((rule.edges : ℝ) ^ (n + 1) - 1) / ((rule.edges : ℝ) - 1) :=
    (eq_div_iff hne).mpr (geom_sum_mul (rule.edges : ℝ) (n + 1))
  rw [hsum]
  ring

end
end Universality.Rule

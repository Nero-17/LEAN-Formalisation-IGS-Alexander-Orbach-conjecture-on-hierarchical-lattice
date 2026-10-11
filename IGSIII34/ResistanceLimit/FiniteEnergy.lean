import IGSIII34.Percolation.SubstitutionTrace
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite quadratic energies before passing to the resistance limit

The edge index is retained in full. In particular the construction does not
discard edges in a dangling branch. Zero coefficients may remove edges, so the
same statements also apply separately to both sides of a noncrossing cell.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.ResistanceLimit
noncomputable section
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Edge]

def finiteEnergy (endpoint : Edge → Vertex × Vertex) (conductance : Edge → ℝ)
    (potential : Vertex → ℝ) : ℝ :=
  ∑ edge, conductance edge * (potential (endpoint edge).1 - potential (endpoint edge).2) ^ 2

def finitePairing (endpoint : Edge → Vertex × Vertex) (conductance : Edge → ℝ)
    (first second : Vertex → ℝ) : ℝ :=
  ∑ edge, conductance edge * (first (endpoint edge).1 - first (endpoint edge).2) *
    (second (endpoint edge).1 - second (endpoint edge).2)

theorem finiteEnergy_nonnegative (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (nonnegative : ∀ edge, 0 ≤ conductance edge)
    (potential : Vertex → ℝ) : 0 ≤ finiteEnergy endpoint conductance potential :=
  Finset.sum_nonneg (fun edge _ => mul_nonneg (nonnegative edge) (sq_nonneg _))

theorem finiteEnergy_constant (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (constant : ℝ) :
    finiteEnergy endpoint conductance (fun _ => constant) = 0 := by
  simp [finiteEnergy]

theorem finiteEnergy_add_constant (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (potential : Vertex → ℝ) (constant : ℝ) :
    finiteEnergy endpoint conductance (fun vertex => potential vertex + constant) =
      finiteEnergy endpoint conductance potential := by
  simp [finiteEnergy]

theorem finiteEnergy_smul (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (potential : Vertex → ℝ) (scalar : ℝ) :
    finiteEnergy endpoint conductance (fun vertex => scalar * potential vertex) =
      scalar ^ 2 * finiteEnergy endpoint conductance potential := by
  unfold finiteEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem finitePairing_self (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (potential : Vertex → ℝ) :
    finitePairing endpoint conductance potential potential = finiteEnergy endpoint conductance potential := by
  unfold finitePairing finiteEnergy
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem finitePairing_comm (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (first second : Vertex → ℝ) :
    finitePairing endpoint conductance first second = finitePairing endpoint conductance second first := by
  unfold finitePairing
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem finitePairing_add_left (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (first second third : Vertex → ℝ) :
    finitePairing endpoint conductance (fun vertex => first vertex + second vertex) third =
      finitePairing endpoint conductance first third + finitePairing endpoint conductance second third := by
  unfold finitePairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem finitePairing_smul_left (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (first second : Vertex → ℝ) (scalar : ℝ) :
    finitePairing endpoint conductance (fun vertex => scalar * first vertex) second =
      scalar * finitePairing endpoint conductance first second := by
  unfold finitePairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem finiteEnergy_add (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (first second : Vertex → ℝ) :
    finiteEnergy endpoint conductance (fun vertex => first vertex + second vertex) =
      finiteEnergy endpoint conductance first + 2 * finitePairing endpoint conductance first second +
        finiteEnergy endpoint conductance second := by
  unfold finiteEnergy finitePairing
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem finiteEnergy_parallelogram (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (first second : Vertex → ℝ) :
    finiteEnergy endpoint conductance (fun vertex => first vertex + second vertex) +
      finiteEnergy endpoint conductance (fun vertex => first vertex - second vertex) =
        2 * finiteEnergy endpoint conductance first + 2 * finiteEnergy endpoint conductance second := by
  unfold finiteEnergy
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem finiteEnergy_normal_contraction (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (nonnegative : ∀ edge, 0 ≤ conductance edge)
    (contraction : ℝ → ℝ) (contracts : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    (potential : Vertex → ℝ) :
    finiteEnergy endpoint conductance (fun vertex => contraction (potential vertex)) ≤
      finiteEnergy endpoint conductance potential := by
  apply Finset.sum_le_sum
  intro edge _
  apply mul_le_mul_of_nonneg_left _ (nonnegative edge)
  exact sq_le_sq.mpr (contracts _ _)

theorem finiteEnergy_add_le (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (nonnegative : ∀ edge, 0 ≤ conductance edge)
    (first second : Vertex → ℝ) :
    finiteEnergy endpoint conductance (fun vertex => first vertex + second vertex) ≤
      2 * finiteEnergy endpoint conductance first + 2 * finiteEnergy endpoint conductance second := by
  have identity := finiteEnergy_parallelogram endpoint conductance first second
  have nonneg := finiteEnergy_nonnegative endpoint conductance nonnegative (fun vertex => first vertex - second vertex)
  linarith

theorem finitePairing_eq_zero_of_edgewise (endpoint : Edge → Vertex × Vertex)
    (conductance : Edge → ℝ) (first second : Vertex → ℝ)
    (vanishes : ∀ edge, conductance edge = 0 ∨ first (endpoint edge).1 = first (endpoint edge).2 ∨
      second (endpoint edge).1 = second (endpoint edge).2) :
    finitePairing endpoint conductance first second = 0 := by
  apply Finset.sum_eq_zero
  intro edge _
  rcases vanishes edge with zero | equal | equal
  · simp [zero]
  · simp [equal]
  · simp [equal]

theorem finiteEnergy_eq_potentialEnergy {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ) (potential : Vertex → ℝ) :
    finiteEnergy network.endpoint (fun edge => (resistance edge)⁻¹) potential =
      network.potentialEnergy resistance potential := by
  unfold finiteEnergy Resistance.FiniteNetwork.potentialEnergy
  apply Finset.sum_congr rfl
  intro edge _
  simp [div_eq_mul_inv, mul_comm]

end
end IGSIII34.ResistanceLimit

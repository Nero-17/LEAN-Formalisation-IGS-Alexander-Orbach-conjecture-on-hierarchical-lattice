import IGSIII.Mass.NormalizedMassPair
import Universality.Matrix.RealDiagonalization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Mass

open Universality Universality.FiniteNetwork Matrix

/-- The columns and inverse rows of a genuine diagonalisation are right and
left eigenvectors. -/
theorem diagonalization_eigenvectors
    (matrix basis inverse : Matrix LiveState LiveState ℝ) (eigenvalues : LiveState → ℝ)
    (inverse_basis : inverse * basis = 1) (basis_inverse : basis * inverse = 1)
    (diagonalization : inverse * matrix * basis = Matrix.diagonal eigenvalues) :
    (∀ state, matrix *ᵥ (fun row => basis row state) =
      eigenvalues state • (fun row => basis row state)) ∧
    (∀ state, (fun column => inverse state column) ᵥ* matrix =
      eigenvalues state • (fun column => inverse state column)) := by
  have right_identity : matrix * basis = basis * Matrix.diagonal eigenvalues := by
    rw [← diagonalization, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      basis_inverse, Matrix.one_mul]
  have left_identity : inverse * matrix = Matrix.diagonal eigenvalues * inverse := by
    rw [← diagonalization, Matrix.mul_assoc, Matrix.mul_assoc, basis_inverse, Matrix.mul_one]
  constructor
  · intro state
    ext row
    have equality := congrFun (congrFun right_identity row) state
    rw [Matrix.mul_diagonal] at equality
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.mul_diagonal,
      Pi.smul_apply, smul_eq_mul, mul_comm] using equality
  · intro state
    ext column
    have equality := congrFun (congrFun left_identity state) column
    rw [Matrix.diagonal_mul] at equality
    simpa only [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_mul,
      Pi.smul_apply, smul_eq_mul] using equality

/-- A normalized Perron vector singles out the first inverse row of the
diagonalisation. This produces a left eigenvector from actual matrix data. -/
theorem normalized_left_from_diagonalization
    (matrix basis inverse : Matrix LiveState LiveState ℝ) (eigenvalues right : LiveState → ℝ)
    (inverse_basis : inverse * basis = 1) (basis_inverse : basis * inverse = 1)
    (diagonalization : inverse * matrix * basis = Matrix.diagonal eigenvalues)
    (right_eigenvector : matrix *ᵥ right = eigenvalues .connected • right)
    (normalized : right .connected = 1)
    (both_distinct : eigenvalues .both ≠ eigenvalues .connected)
    (single_distinct : eigenvalues .single ≠ eigenvalues .connected) :
    ∃ coefficient : ℝ, coefficient ≠ 0 ∧
      right = coefficient • (fun row => basis row .connected) ∧
      (fun column => inverse .connected column / coefficient) ᵥ* matrix =
        eigenvalues .connected • (fun column => inverse .connected column / coefficient) ∧
      (fun column => inverse .connected column / coefficient) ⬝ᵥ right = 1 := by
  have eigenvectors := diagonalization_eigenvectors matrix basis inverse eigenvalues
    inverse_basis basis_inverse diagonalization
  have transformed : Matrix.diagonal eigenvalues *ᵥ (inverse *ᵥ right) =
      eigenvalues .connected • (inverse *ᵥ right) := by
    rw [← diagonalization]
    simp only [← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec right basis inverse, basis_inverse, Matrix.one_mulVec,
      right_eigenvector, Matrix.mulVec_smul]
  have other_zero (state : LiveState) (distinct : eigenvalues state ≠ eigenvalues .connected) :
      (inverse *ᵥ right) state = 0 := by
    have equality := congrFun transformed state
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at equality
    exact (mul_eq_zero.mp (show (eigenvalues state - eigenvalues .connected) *
      (inverse *ᵥ right) state = 0 by nlinarith)).resolve_left (sub_ne_zero.mpr distinct)
  have reconstruction : right = (inverse *ᵥ right) .connected • (fun row => basis row .connected) := by
    have identity : basis *ᵥ (inverse *ᵥ right) = right := by
      rw [Matrix.mulVec_mulVec, basis_inverse, Matrix.one_mulVec]
    ext row
    calc
      right row = (basis *ᵥ (inverse *ᵥ right)) row := congrFun identity.symm row
      _ = ((inverse *ᵥ right) .connected • (fun row => basis row .connected)) row := by
        change (∑ state, basis row state * (inverse *ᵥ right) state) = _
        simp only [sum_liveState, Pi.smul_apply, smul_eq_mul,
      other_zero .both both_distinct, other_zero .single single_distinct, mul_zero, add_zero]
        ring
  have coefficient_nonzero : (inverse *ᵥ right) .connected ≠ 0 := by
    intro zero
    have equality := congrFun reconstruction .connected
    simp only [Pi.smul_apply, smul_eq_mul, zero, zero_mul, normalized] at equality
    norm_num at equality
  refine ⟨(inverse *ᵥ right) .connected, coefficient_nonzero, reconstruction, ?_, ?_⟩
  · have equality := eigenvectors.2 .connected
    ext column
    have entry := congrFun equality column
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at entry ⊢
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, entry]
    ring
  · simp only [dotProduct, div_mul_eq_mul_div, ← Finset.sum_div]
    change (inverse *ᵥ right) .connected / (inverse *ᵥ right) .connected = 1
    exact div_self coefficient_nonzero

/-- A nonnegative normalized left Perron vector is strictly positive when
an actual power of the offspring matrix is strictly positive. -/
theorem left_perron_positive_of_positive_power
    (matrix : Matrix LiveState LiveState ℝ) (left right : LiveState → ℝ) (radius : ℝ)
    (radius_positive : 0 < radius) (left_nonnegative : ∀ state, 0 ≤ left state)
    (left_eigenvector : left ᵥ* matrix = radius • left)
    (normalized : left ⬝ᵥ right = 1)
    (power_positive : ∀ state child, 0 < (matrix ^ 4) state child) :
    ∀ child, 0 < left child := by
  have some_positive : ∃ state, 0 < left state := by
    by_contra absent
    push_neg at absent
    have left_zero : left = 0 := by
      ext state
      exact le_antisymm (absent state) (left_nonnegative state)
    simp only [left_zero, zero_dotProduct] at normalized
    norm_num at normalized
  obtain ⟨state, state_positive⟩ := some_positive
  have powered : ∀ n : ℕ, left ᵥ* matrix ^ n = radius ^ n • left := by
    intro n
    induction n with
    | zero => simp
    | succ n induction_hypothesis =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, induction_hypothesis,
        Matrix.smul_vecMul, left_eigenvector, smul_smul, ← pow_succ]
  intro child
  have positive_sum : 0 < (left ᵥ* matrix ^ 4) child := by
    change 0 < ∑ parent, left parent * (matrix ^ 4) parent child
    apply Finset.sum_pos'
    · intro parent _
      exact mul_nonneg (left_nonnegative parent) (power_positive parent child).le
    · exact ⟨state, Finset.mem_univ state, mul_pos state_positive (power_positive state child)⟩
  rw [powered] at positive_sum
  exact (mul_pos_iff_of_pos_left (pow_pos radius_positive 4)).mp positive_sum

end IGSIII.Mass

namespace Universality.Rule.ConfigurationHistory

open FiniteNetwork Matrix

/-- The three coordinates count actual live edges of the current graph. -/
noncomputable def populationVector (rule : Rule) (state : LiveState) (n : ℕ)
    (history : rule.ConfigurationHistory n) : LiveState → ℝ :=
  fun child => ((rule.generation n).network.liveCount state child (latest rule n history) : ℝ)

theorem weightedPopulation_eq_dotProduct (rule : Rule) (state : LiveState)
    (values : LiveState → ℝ) (n : ℕ) (history : rule.ConfigurationHistory n) :
    weightedPopulation rule state values n history = populationVector rule state n history ⬝ᵥ values :=
  (rule.generation n).network.liveResponse_eq state (latest rule n history) values

/-- Exact reconstruction of actual populations in an eigenbasis, before
taking any almost-sure limits. -/
theorem populationVector_eigenbasis_reconstruction (rule : Rule) (state : LiveState)
    (basis inverse : Matrix LiveState LiveState ℝ) (basis_inverse : basis * inverse = 1)
    (right : LiveState → ℝ) (coefficient : ℝ) (coefficient_nonzero : coefficient ≠ 0)
    (right_column : right = coefficient • (fun row => basis row .connected))
    (n : ℕ) (history : rule.ConfigurationHistory n) (child : LiveState) :
    populationVector rule state n history child =
      weightedPopulation rule state right n history * (inverse .connected child / coefficient) +
      weightedPopulation rule state (fun row => basis row .both) n history * inverse .both child +
      weightedPopulation rule state (fun row => basis row .single) n history * inverse .single child := by
  have identity : (populationVector rule state n history ᵥ* basis) ᵥ* inverse =
      populationVector rule state n history := by
    rw [Matrix.vecMul_vecMul, basis_inverse, Matrix.vecMul_one]
  rw [right_column, weightedPopulation_smul]
  simp_rw [weightedPopulation_eq_dotProduct]
  have equality := congrFun identity child
  simp only [Matrix.vecMul, dotProduct, sum_liveState] at equality ⊢
  rw [← equality]
  field_simp [coefficient_nonzero]

end Universality.Rule.ConfigurationHistory

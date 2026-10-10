import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Strict Perron row comparison in the mass/core argument

A positive eigenvector and a positive off-diagonal entry force the eigenvalue
strictly above the corresponding diagonal entry. The probabilistic mass
matrix, its Perron vector and the relevant live-child event are not assumed to
have been constructed by this numerical lemma.
-/

set_option autoImplicit false

namespace IGSIII34.AO

theorem perron_strictly_above_diagonal {State : Type*} [Fintype State]
    [DecidableEq State] (matrix : State → State → ℝ) (vector : State → ℝ)
    {growth : ℝ} (nonnegative : ∀ first second, 0 ≤ matrix first second)
    (positiveVector : ∀ state, 0 < vector state)
    (eigenvector : ∀ first, ∑ second, matrix first second * vector second =
      growth * vector first)
    {connected other : State} (distinct : other ≠ connected)
    (positiveOffDiagonal : 0 < matrix connected other) :
    matrix connected connected < growth := by
  have rowStrict : matrix connected connected * vector connected <
      ∑ second, matrix connected second * vector second :=
    Finset.single_lt_sum distinct (Finset.mem_univ connected) (Finset.mem_univ other)
      (mul_pos positiveOffDiagonal (positiveVector other))
      (fun second _ _ => mul_nonneg (nonnegative connected second) (positiveVector second).le)
  rw [eigenvector] at rowStrict
  exact (mul_lt_mul_iff_of_pos_right (positiveVector connected)).mp rowStrict

theorem full_mass_strictly_above_core {State : Type*} [Fintype State]
    [DecidableEq State] (matrix : State → State → ℝ) (vector : State → ℝ)
    {growth coreGrowth : ℝ} (nonnegative : ∀ first second, 0 ≤ matrix first second)
    (positiveVector : ∀ state, 0 < vector state)
    (eigenvector : ∀ first, ∑ second, matrix first second * vector second =
      growth * vector first)
    {connected other : State} (distinct : other ≠ connected)
    (positiveOffDiagonal : 0 < matrix connected other)
    (coreIncluded : coreGrowth ≤ matrix connected connected) :
    coreGrowth < growth :=
  coreIncluded.trans_lt (perron_strictly_above_diagonal matrix vector nonnegative
    positiveVector eigenvector distinct positiveOffDiagonal)

end IGSIII34.AO

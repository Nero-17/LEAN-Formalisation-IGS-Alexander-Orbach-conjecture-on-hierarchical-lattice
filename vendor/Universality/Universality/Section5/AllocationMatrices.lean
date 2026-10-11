import Universality.Section5.AllocationScalars
import Universality.Section5.WheatstoneMassKernels
import Universality.Algebra.PacketCancellation
import Universality.Matrix.MassPlane
import Mathlib.Tactic.NoncommRing

/-! Ordered algebraic allocation responses. The identification with the actual
graph mass matrix requires the separate graph recursion and terminal symmetries.
No commutativity of the two kernels is assumed. -/

namespace Universality.Section5
noncomputable section
open Matrix FiniteNetwork

def WheatstoneExpression.matrixResponse {R : Type*} [Semiring R] (outer central : R) :
    WheatstoneExpression → R
  | .edge => 1
  | .node a b c => outer * a.matrixResponse outer central +
      outer * b.matrixResponse outer central + central * c.matrixResponse outer central

theorem allocatedExpression_matrixResponse {R : Type*} [Ring R] (outer central : R)
    (n : ℕ) (decorated : List (Fin 3) → Bool) :
    (allocatedExpression n decorated).matrixResponse outer central =
      (outer + outer + central) ^ n +
        decoratedLeafWeight outer central n decorated * (outer + outer + central - 1) := by
  induction n generalizing decorated with
  | zero =>
      cases value : decorated [] <;>
        simp [allocatedExpression, value, WheatstoneExpression.matrixResponse, decoratedLeafWeight]
  | succ n induction_hypothesis =>
      simp only [allocatedExpression, WheatstoneExpression.matrixResponse,
        induction_hypothesis, decoratedLeafWeight, pow_succ']
      noncomm_ring

theorem allocatedExpression_matrixResponse_ordered_sum {R : Type*} [Ring R] (outer central : R)
    (n : ℕ) (decorated : List (Fin 3) → Bool) :
    (allocatedExpression n decorated).matrixResponse outer central =
      (2 * outer + central) ^ n +
        ((ternaryAddresses n).map (fun address => if decorated address then
          addressWeight outer central address * (2 * outer + central - 1) else 0)).sum := by
  rw [allocatedExpression_matrixResponse, decoratedLeafWeight_eq_sum]
  simp only [two_mul]
  congr 1
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro address _
  cases decorated address <;> simp

/-- The ternary branches A and B both project to the outer binary letter. -/
def projectedAddress (address : List (Fin 3)) : List Bool :=
  address.map (fun letter => decide (letter = 2))

theorem addressWeight_eq_wordProduct {R : Type*} [Monoid R] (outer central : R)
    (address : List (Fin 3)) :
    addressWeight outer central address = wordProduct outer central (projectedAddress address) := by
  induction address with
  | nil => rfl
  | cons letter address induction_hypothesis =>
      by_cases isCentral : letter = 2
      · simp [addressWeight, projectedAddress, isCentral, wordProduct, induction_hypothesis]
      · simp [addressWeight, projectedAddress, isCentral, wordProduct, induction_hypothesis]

theorem K3real_massPlaneBlock :
    massPlaneBlock K3real = (1 / 16 : ℝ) • outerKernelNumerator.map Int.cast := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [massPlaneBlock, K3real, outerPairKernel, outerPairKernelCount,
      outerKernelNumerator, Matrix.map_apply]

theorem J3real_massPlaneBlock :
    massPlaneBlock J3real = (1 / 16 : ℝ) • centralKernelNumerator.map Int.cast := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [massPlaneBlock, J3real, centralKernel, centralKernelCount,
      centralKernelNumerator, Matrix.map_apply]

theorem K3real_preservesMassPlane : PreservesMassPlane K3real :=
  outerPairKernel_preservesMassPlane

theorem J3real_preservesMassPlane : PreservesMassPlane J3real :=
  centralKernel_preservesMassPlane

theorem K3real_massPlaneLift (value : Fin 2 → ℝ) :
    K3real *ᵥ massPlaneLift value =
      (1 / 16 : ℝ) • massPlaneLift (outerKernelNumerator.map Int.cast *ᵥ value) := by
  rw [K3real_preservesMassPlane value, K3real_massPlaneBlock,
    Matrix.smul_mulVec, massPlaneLift_smul]

theorem J3real_massPlaneLift (value : Fin 2 → ℝ) :
    J3real *ᵥ massPlaneLift value =
      (1 / 16 : ℝ) • massPlaneLift (centralKernelNumerator.map Int.cast *ᵥ value) := by
  rw [J3real_preservesMassPlane value, J3real_massPlaneBlock,
    Matrix.smul_mulVec, massPlaneLift_smul]

/-- Every ordered word retains its order and contributes exactly one factor
of 1/16 for each letter when lifted from the integer numerator kernels. -/
theorem wordProduct_massPlaneLift (word : List Bool) (value : Fin 2 → ℝ) :
    wordProduct K3real J3real word *ᵥ massPlaneLift value =
      (1 / 16 : ℝ) ^ word.length • massPlaneLift
        (wordProduct (outerKernelNumerator.map Int.cast)
          (centralKernelNumerator.map Int.cast) word *ᵥ value) := by
  induction word with
  | nil => simp [wordProduct]
  | cons letter word induction_hypothesis =>
      cases letter <;>
        simp only [wordProduct, List.length_cons, ← Matrix.mulVec_mulVec,
          induction_hypothesis, Matrix.mulVec_smul, K3real_massPlaneLift,
          J3real_massPlaneLift, smul_smul, pow_succ]

end
end Universality.Section5

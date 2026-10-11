import Universality.Matrix.CriticalBlockDecomposition
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-! The actual conditional counting matrix is defined over ℚ(p). -/

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators
open IntermediateField

variable {vertices edges : ℕ}

theorem bernoulliWeight_mem_field (field : IntermediateField ℚ ℝ)
    {p : ℝ} (hp : p ∈ field) (ω : Configuration edges) :
    bernoulliWeight p ω ∈ field := by
  apply field.prod_mem
  intro e _
  split
  · exact hp
  · exact field.sub_mem field.one_mem hp

theorem reliability_mem_field (R : FiniteNetwork vertices edges)
    (field : IntermediateField ℚ ℝ) {p : ℝ} (hp : p ∈ field) :
    R.reliability p ∈ field := by
  apply field.sum_mem
  intro ω _
  split
  · exact bernoulliWeight_mem_field field hp ω
  · exact field.zero_mem

theorem conditioningProbability_mem_field (R : FiniteNetwork vertices edges)
    (field : IntermediateField ℚ ℝ) {p : ℝ} (hp : p ∈ field) (σ : LiveState) :
    R.conditioningProbability p σ ∈ field := by
  apply field.sum_mem
  intro ω _
  split
  · exact bernoulliWeight_mem_field field hp ω
  · exact field.zero_mem

theorem massMatrix_mem_field (R : FiniteNetwork vertices edges)
    (field : IntermediateField ℚ ℝ) {p : ℝ} (hp : p ∈ field) (σ τ : LiveState) :
    R.massMatrix p σ τ ∈ field := by
  apply field.div_mem
  · apply field.sum_mem
    intro ω _
    split
    · exact field.mul_mem (bernoulliWeight_mem_field field hp ω) (field.natCast_mem _)
    · exact field.zero_mem
  · exact R.conditioningProbability_mem_field field hp σ

theorem massMatrix_mem_adjoin (R : FiniteNetwork vertices edges) (p : ℝ)
    (σ τ : LiveState) : R.massMatrix p σ τ ∈ ℚ⟮p⟯ :=
  R.massMatrix_mem_field _ (mem_adjoin_simple_self ℚ p) σ τ

theorem massPlaneBlock_mem_adjoin (R : FiniteNetwork vertices edges) (p : ℝ)
    (i j : Fin 2) : Universality.massPlaneBlock (R.massMatrix p) i j ∈ ℚ⟮p⟯ := by
  fin_cases i <;> fin_cases j
  · exact R.massMatrix_mem_adjoin p _ _
  · exact (ℚ⟮p⟯).add_mem
      ((ℚ⟮p⟯).mul_mem ((ℚ⟮p⟯).natCast_mem 2) (R.massMatrix_mem_adjoin p _ _))
      (R.massMatrix_mem_adjoin p _ _)
  · exact R.massMatrix_mem_adjoin p _ _
  · exact (ℚ⟮p⟯).add_mem
      ((ℚ⟮p⟯).mul_mem ((ℚ⟮p⟯).natCast_mem 2) (R.massMatrix_mem_adjoin p _ _))
      (R.massMatrix_mem_adjoin p _ _)

end
end Universality.FiniteNetwork

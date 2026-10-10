import Universality.Matrix.RealDiagonalization

namespace Universality
noncomputable section
open Matrix FiniteNetwork

theorem positiveRoot_eq_of_trace_det (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (htrace : A.trace = B.trace) (hdet : A.det = B.det) : positiveRoot A = positiveRoot B := by
  have hdisc (M : Matrix (Fin 2) (Fin 2) ℝ) :
      (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 = M.trace ^ 2 - 4 * M.det := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  unfold positiveRoot
  rw [hdisc, hdisc, ← Matrix.trace_fin_two, ← Matrix.trace_fin_two, htrace, hdet]

/-- Equal block trace, determinant and pivotal response give an explicit real
similarity. The pivotal eigenvalue may equal the secondary block eigenvalue. -/
theorem real_similarity_of_critical_blocks (A B : Matrix LiveState LiveState ℝ)
    (p q response : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hplaneA : PreservesMassPlane A) (hplaneB : PreservesMassPlane B)
    (heigenA : A *ᵥ pivotalRightVector p = response • pivotalRightVector p)
    (heigenB : B *ᵥ pivotalRightVector q = response • pivotalRightVector q)
    (hblockA : ∀ i j, 0 < massPlaneBlock A i j)
    (hblockB : ∀ i j, 0 < massPlaneBlock B i j)
    (htrace : (massPlaneBlock A).trace = (massPlaneBlock B).trace)
    (hdet : (massPlaneBlock A).det = (massPlaneBlock B).det) :
    ∃ basis inverse : Matrix LiveState LiveState ℝ,
      inverse * basis = 1 ∧ basis * inverse = 1 ∧ inverse * A * basis = B := by
  have hroot := positiveRoot_eq_of_trace_det _ _ htrace hdet
  have hvalues : blockEigenvalues (massPlaneBlock A) response =
      blockEigenvalues (massPlaneBlock B) response := by
    funext state
    cases state <;> simp only [blockEigenvalues, secondaryRoot, hroot, htrace]
  obtain ⟨basisA, inverseA, hleftA, hrightA, hdiagA⟩ :=
    real_diagonalization_of_critical_block A p response hp hplaneA heigenA hblockA
  obtain ⟨basisB, inverseB, hleftB, hrightB, hdiagB⟩ :=
    real_diagonalization_of_critical_block B q response hq hplaneB heigenB hblockB
  refine ⟨basisA * inverseB, basisB * inverseA, ?_, ?_, ?_⟩
  · calc
      _ = basisB * (inverseA * basisA) * inverseB := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hleftA, Matrix.mul_one, hrightB]
  · calc
      _ = basisA * (inverseB * basisB) * inverseA := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hleftB, Matrix.mul_one, hrightA]
  · calc
      _ = basisB * (inverseA * A * basisA) * inverseB := by simp only [Matrix.mul_assoc]
      _ = basisB * (inverseB * B * basisB) * inverseB := by rw [hdiagA, hvalues, hdiagB]
      _ = (basisB * inverseB) * B * (basisB * inverseB) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hrightB, Matrix.one_mul, Matrix.mul_one]

end
end Universality

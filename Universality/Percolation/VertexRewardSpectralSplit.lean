import Universality.Percolation.VertexMeanLimit

namespace Universality
noncomputable section
open FiniteNetwork Matrix

theorem massPlaneLift_add (first second : Fin 2 → ℝ) :
    massPlaneLift (first + second) = massPlaneLift first + massPlaneLift second := by
  funext state
  cases state <;> simp [massPlaneLift, mul_add]

theorem massPlane_complement_reward_eigenvector (M : Matrix LiveState LiveState ℝ)
    (hplane : PreservesMassPlane M) (hblock : ∀ i j, 0 < massPlaneBlock M i j) (reward : Fin 2 → ℝ) :
    M *ᵥ massPlaneLift ((1 - perronProjection (massPlaneBlock M)) *ᵥ reward) =
      secondaryRoot (massPlaneBlock M) • massPlaneLift ((1 - perronProjection (massPlaneBlock M)) *ᵥ reward) := by
  rw [hplane, Matrix.mulVec_mulVec, mul_complement_perronProjection _ hblock,
    Matrix.smul_mulVec, massPlaneLift_smul]

namespace Rule

/-- The true one-cell reward splits into a positive Perron component and a
real complementary eigen-component with strictly smaller eigenvalue modulus. -/
theorem Classical.vertex_reward_spectral_split {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    ∃ perron remainder : LiveState → ℝ, ∃ eigenvalue : ℝ,
      (∀ state, 0 < perron state) ∧ rule.network.conditionalVertexMass p = perron + remainder ∧
      rule.network.massMatrix p *ᵥ perron =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • perron ∧
      rule.network.massMatrix p *ᵥ remainder = eigenvalue • remainder ∧
      |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp' (h.connected _) h.scale h.cut).1
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  have hspectral : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal =
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) := by
    rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
      ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  rw [hspectral]
  let reward : Fin 2 → ℝ := ![rule.network.conditionalVertexMass p .connected,
    rule.network.conditionalVertexMass p .single]
  refine ⟨massPlaneLift (perronProjection (massPlaneBlock (rule.network.massMatrix p)) *ᵥ reward),
    massPlaneLift ((1 - perronProjection (massPlaneBlock (rule.network.massMatrix p))) *ᵥ reward),
    secondaryRoot (massPlaneBlock (rule.network.massMatrix p)), ?_, ?_,
    massPlane_projected_reward_eigenvector _ hplane hblock reward,
    massPlane_complement_reward_eigenvector _ hplane hblock reward, secondaryRoot_abs_lt _ hblock⟩
  · apply massPlaneLift_pos
    apply perronProjection_mulVec_pos _ hblock
    intro i
    fin_cases i <;> exact rule.network.conditionalVertexMass_pos hp hp' (h.connected _) h.scale _
  · rw [← massPlaneLift_add, ← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    exact rule.network.conditionalVertexMass_in_massPlane p symmetry hs ht

end Rule
end
end Universality

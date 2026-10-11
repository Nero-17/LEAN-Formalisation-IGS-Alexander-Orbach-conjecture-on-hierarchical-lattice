import Universality.Matrix.PerronPowerLimit
import Universality.Matrix.MassPlane

namespace Universality
noncomputable section
open Matrix FiniteNetwork Filter
open scoped Topology

theorem massPlane_power_mulVec (M : Matrix LiveState LiveState ℝ)
    (hplane : PreservesMassPlane M) (reward : Fin 2 → ℝ) (n : ℕ) :
    M ^ n *ᵥ massPlaneLift reward = massPlaneLift (massPlaneBlock M ^ n *ᵥ reward) := by
  rw [hplane.pow n, massPlaneBlock_pow M hplane n]

theorem massPlane_affine_sum_limit (M : Matrix LiveState LiveState ℝ)
    (hplane : PreservesMassPlane M) (hblock : ∀ i j, 0 < massPlaneBlock M i j)
    (hradius : 1 < positiveRoot (massPlaneBlock M)) (reward : Fin 2 → ℝ)
    (state : LiveState) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (M ^ k *ᵥ massPlaneLift reward) state) /
      positiveRoot (massPlaneBlock M) ^ n) atTop
      (𝓝 ((positiveRoot (massPlaneBlock M) / (positiveRoot (massPlaneBlock M) - 1)) *
        massPlaneLift (perronProjection (massPlaneBlock M) *ᵥ reward) state)) := by
  simp_rw [massPlane_power_mulVec M hplane]
  cases state
  · exact positive_matrix_affine_sum_limit _ hblock hradius reward 0
  · simp only [massPlaneLift, ← Finset.mul_sum, mul_div_assoc]
    convert (positive_matrix_affine_sum_limit _ hblock hradius reward 1).const_mul 2 using 1 <;> ring
  · exact positive_matrix_affine_sum_limit _ hblock hradius reward 1

theorem massPlane_projected_reward_eigenvector (M : Matrix LiveState LiveState ℝ)
    (hplane : PreservesMassPlane M) (hblock : ∀ i j, 0 < massPlaneBlock M i j)
    (reward : Fin 2 → ℝ) :
    M *ᵥ massPlaneLift (perronProjection (massPlaneBlock M) *ᵥ reward) =
      positiveRoot (massPlaneBlock M) • massPlaneLift (perronProjection (massPlaneBlock M) *ᵥ reward) := by
  rw [hplane, Matrix.mulVec_mulVec, mul_perronProjection _ hblock, Matrix.smul_mulVec,
    massPlaneLift_smul]

end
end Universality

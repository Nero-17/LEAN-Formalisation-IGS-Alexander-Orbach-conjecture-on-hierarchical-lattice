import Universality.Percolation.VertexMassPlane
import Universality.Percolation.VertexMassGrowth
import Universality.Matrix.MassPlaneLimit

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

/-- The actual accumulated internal-vertex means converge after normalization.
The limiting vector is strictly positive and belongs to the Perron eigenspace. -/
theorem Classical.internal_vertex_mean_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : LiveState → ℝ, (∀ state, 0 < limit state) ∧
      rule.network.massMatrix p *ᵥ limit =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • limit ∧
      ∀ state, Tendsto (fun n : ℕ => (rule.generation n).network.conditionalVertexMass p state /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (limit state)) := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp' (h.connected _) h.scale h.cut).1
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  have hradius : 1 < positiveRoot (massPlaneBlock (rule.network.massMatrix p)) :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.network.pivotal_response_lt_mass_root p hfixed hp hp' hblock)
  have hspectral : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal =
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) := by
    rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
      ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  rw [hspectral]
  let reward : Fin 2 → ℝ := ![rule.network.conditionalVertexMass p .connected,
    rule.network.conditionalVertexMass p .single]
  let projected := massPlaneLift (perronProjection (massPlaneBlock (rule.network.massMatrix p)) *ᵥ reward)
  have hreward : ∀ i, 0 < reward i := by
    intro i
    fin_cases i <;> exact rule.network.conditionalVertexMass_pos hp hp' (h.connected _) h.scale _
  have hprojected : ∀ state, 0 < projected state :=
    massPlaneLift_pos _ (perronProjection_mulVec_pos _ hblock reward hreward)
  have heigen := massPlane_projected_reward_eigenvector _ hplane hblock reward
  refine ⟨(positiveRoot (massPlaneBlock (rule.network.massMatrix p)) /
    (positiveRoot (massPlaneBlock (rule.network.massMatrix p)) - 1)) • projected, ?_, ?_, ?_⟩
  · intro state
    exact mul_pos (div_pos (lt_trans zero_lt_one hradius) (sub_pos.mpr hradius)) (hprojected state)
  · rw [Matrix.mulVec_smul, heigen]
    module
  · intro state
    convert massPlane_affine_sum_limit _ hplane hblock hradius reward state using 1
    · congr 1
      funext n
      rw [rule.generation_conditionalVertexMass p hfixed hp hp' symmetry hs ht,
        rule.network.conditionalVertexMass_in_massPlane p symmetry hs ht]
    · rfl

end
end Universality.Rule

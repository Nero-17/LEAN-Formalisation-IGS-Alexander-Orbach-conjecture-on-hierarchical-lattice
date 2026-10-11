import Universality.Percolation.VertexMassIteration
import Universality.Percolation.VertexMassPositivity
import Universality.Matrix.AffineGrowth
import Universality.Percolation.ClassicalCriticalPoint

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

/-- The first-moment assertion in the conditional internal-mass lemma.
All three means count actual vertices, with both outer terminals excluded.
The constants are uniform in the generation and the three states. -/
theorem Classical.internal_vertex_mass_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ n σ, lower *
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n ≤
          (rule.generation n).network.conditionalVertexMass p σ ∧
        (rule.generation n).network.conditionalVertexMass p σ ≤ upper *
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n := by
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp' (h.connected _) h.scale h.cut).1
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hs ht
  have hr : 1 < positiveRoot (massPlaneBlock (rule.network.massMatrix p)) :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.network.pivotal_response_lt_mass_root p hfixed hp hp' hblock)
  have hweight : ∀ σ, 0 < massPlaneLift
      ![massPlaneBlock (rule.network.massMatrix p) 0 1,
        positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          massPlaneBlock (rule.network.massMatrix p) 0 0] σ := by
    apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := affine_matrix_sum_bounds
    (rule.network.massMatrix p)
    (massPlaneLift ![massPlaneBlock (rule.network.massMatrix p) 0 1,
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
        massPlaneBlock (rule.network.massMatrix p) 0 0])
    (rule.network.conditionalVertexMass p)
    (positiveRoot (massPlaneBlock (rule.network.massMatrix p)))
    (rule.network.massMatrix_nonneg hp.le hp'.le) hweight
    (rule.network.conditionalVertexMass_pos hp hp' (h.connected _) h.scale) hr
    (by rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul])
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro n σ
  rw [rule.generation_conditionalVertexMass p hfixed hp hp' symmetry hs ht,
    massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  exact hbounds n σ

theorem Classical.internal_vertex_mass_logarithmic_growth {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (σ : LiveState) :
    Tendsto (fun n : ℕ => Real.log ((rule.generation n).network.conditionalVertexMass p σ) / n)
      atTop (𝓝 (Real.log
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := h.internal_vertex_mass_bounds p hp hp' hfixed
  have hr := (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
    (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  exact logarithmic_growth_of_bounds _ _ lower upper (lt_trans zero_lt_one hr)
    hlower hupper (fun n => hbounds n σ)

end
end Universality.Rule

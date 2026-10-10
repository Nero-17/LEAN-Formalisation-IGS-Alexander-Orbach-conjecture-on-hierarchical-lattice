import Universality.Graph.DirichletEnergy
namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {v e w f : ℕ} (R : FiniteNetwork v e) (S : FiniteNetwork w f)

def liftedUnitPotential (outer : Fin v → ℝ) (inner : Fin w → ℝ) :
    Fin (Fintype.card (R.SubstitutionVertex S)) → ℝ := fun vertex =>
  match (Fintype.equivFin (R.SubstitutionVertex S)).symm vertex with
  | Sum.inl old => outer old
  | Sum.inr pair => outer (R.endpoint pair.1).2 +
      (outer (R.endpoint pair.1).1 - outer (R.endpoint pair.1).2) * inner pair.2.val

theorem liftedUnitPotential_old (outer : Fin v → ℝ) (inner : Fin w → ℝ) (vertex : Fin v) :
    R.liftedUnitPotential S outer inner (Fintype.equivFin _ (Sum.inl vertex)) = outer vertex := by
  simp only [liftedUnitPotential, Equiv.symm_apply_apply]

theorem liftedUnitPotential_cell (outer : Fin v → ℝ) (inner : Fin w → ℝ)
    (hs : inner S.source = 1) (ht : inner S.target = 0) (edge : Fin e) (vertex : Fin w) :
    R.liftedUnitPotential S outer inner (Fintype.equivFin _ (R.cellVertex S edge vertex)) =
      (outer (R.endpoint edge).1 - outer (R.endpoint edge).2) * inner vertex + outer (R.endpoint edge).2 := by
  by_cases hsource : vertex = S.source
  · subst vertex
    rw [R.cellVertex_source, R.liftedUnitPotential_old, hs]
    ring
  · by_cases htarget : vertex = S.target
    · subst vertex
      rw [R.cellVertex_target, R.liftedUnitPotential_old, ht]
      ring
    · simp only [liftedUnitPotential, cellVertex, dif_neg hsource, dif_neg htarget, Equiv.symm_apply_apply]
      ring

theorem substitute_dirichletEnergy (potential : Fin (Fintype.card (R.SubstitutionVertex S)) → ℝ) :
    (R.substitute S).dirichletEnergy potential =
      ∑ edge : Fin e, S.dirichletEnergy (fun vertex => potential (Fintype.equivFin _ (R.cellVertex S edge vertex))) := by
  unfold dirichletEnergy
  change (∑ edge, (potential ((R.substitute S).endpoint edge).1 - potential ((R.substitute S).endpoint edge).2) ^ 2) =
    ∑ edge : Fin e, ∑ inner : Fin f,
      (potential (Fintype.equivFin _ (R.cellVertex S edge (S.endpoint inner).1)) -
       potential (Fintype.equivFin _ (R.cellVertex S edge (S.endpoint inner).2))) ^ 2
  rw [← Fintype.sum_prod_type (fun pair : Fin e × Fin f =>
      (potential (Fintype.equivFin _ (R.cellVertex S pair.1 (S.endpoint pair.2).1)) -
       potential (Fintype.equivFin _ (R.cellVertex S pair.1 (S.endpoint pair.2).2))) ^ 2)]
  apply Fintype.sum_equiv finProdFinEquiv.symm
  intro edge
  simp only [substitute, Equiv.symm_apply_apply]

theorem liftedUnitPotential_energy (outer : Fin v → ℝ) (inner : Fin w → ℝ)
    (hs : inner S.source = 1) (ht : inner S.target = 0) :
    (R.substitute S).dirichletEnergy (R.liftedUnitPotential S outer inner) =
      R.dirichletEnergy outer * S.dirichletEnergy inner := by
  rw [R.substitute_dirichletEnergy]
  simp_rw [R.liftedUnitPotential_cell S outer inner hs ht]
  simp_rw [S.dirichletEnergy_affine]
  exact (Finset.sum_mul _ _ _).symm

end
end Universality.FiniteNetwork

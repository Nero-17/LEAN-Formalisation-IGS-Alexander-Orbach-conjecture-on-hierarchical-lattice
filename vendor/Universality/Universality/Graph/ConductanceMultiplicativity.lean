import Universality.Graph.SubstitutionEnergy
namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {v e w f : ℕ} (R : FiniteNetwork v e) (S : FiniteNetwork w f)

theorem substitute_unitConductance :
    (R.substitute S).unitConductance = R.unitConductance * S.unitConductance := by
  apply le_antisymm
  · rw [mul_comm R.unitConductance S.unitConductance]
    apply R.le_scaled_unitConductance S.unitConductance _ S.unitConductance_nonneg
    intro outer hs ht
    rw [mul_comm S.unitConductance (R.dirichletEnergy outer)]
    apply S.le_scaled_unitConductance (R.dirichletEnergy outer) _ (R.dirichletEnergy_nonneg outer)
    intro inner hsource htarget
    rw [← R.liftedUnitPotential_energy S outer inner hsource htarget]
    apply (R.substitute S).unitConductance_le_energy
    · exact (R.liftedUnitPotential_old S outer inner R.source).trans hs
    · exact (R.liftedUnitPotential_old S outer inner R.target).trans ht
  · apply (R.substitute S).le_unitConductance
    intro potential hs ht
    let coarse : Fin v → ℝ := fun vertex => potential (Fintype.equivFin _ (Sum.inl vertex))
    have hcoarseS : coarse R.source = 1 := hs
    have hcoarseT : coarse R.target = 0 := ht
    calc
      R.unitConductance * S.unitConductance ≤ R.dirichletEnergy coarse * S.unitConductance :=
        mul_le_mul_of_nonneg_right (R.unitConductance_le_energy coarse hcoarseS hcoarseT) S.unitConductance_nonneg
      _ = ∑ edge : Fin e, S.unitConductance * (coarse (R.endpoint edge).1 - coarse (R.endpoint edge).2) ^ 2 := by
        unfold dirichletEnergy
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro edge _
        ring
      _ ≤ (R.substitute S).dirichletEnergy potential := by
        rw [R.substitute_dirichletEnergy]
        apply Finset.sum_le_sum
        intro edge _
        simpa only [R.cellVertex_source, R.cellVertex_target] using
          S.scaled_unitConductance_le_energy (fun vertex => potential (Fintype.equivFin _ (R.cellVertex S edge vertex)))

theorem substitute_unitEffectiveResistance
    (hR : R.fullGraph.Reachable R.source R.target) (hS : S.fullGraph.Reachable S.source S.target)
    (hsub : (R.substitute S).fullGraph.Reachable (R.substitute S).source (R.substitute S).target) :
    (R.substitute S).unitEffectiveResistance hsub = R.unitEffectiveResistance hR * S.unitEffectiveResistance hS := by
  unfold unitEffectiveResistance
  rw [R.substitute_unitConductance, mul_inv_rev,
    mul_comm S.unitConductance⁻¹ R.unitConductance⁻¹]

end
end Universality.FiniteNetwork

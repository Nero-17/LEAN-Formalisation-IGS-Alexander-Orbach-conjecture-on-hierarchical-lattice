import Universality.Graph.Rule
import Universality.Graph.DistanceCertificate
import Mathlib.Algebra.Order.Field.Basic

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
open Set
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def dirichletEnergy (potential : Fin vertices → ℝ) : ℝ :=
  ∑ edge, (potential (R.endpoint edge).1 - potential (R.endpoint edge).2) ^ 2

def unitPotentialEnergies : Set ℝ :=
  {energy | ∃ potential : Fin vertices → ℝ,
    potential R.source = 1 ∧ potential R.target = 0 ∧ R.dirichletEnergy potential = energy}

def unitConductance : ℝ := sInf R.unitPotentialEnergies

/-- The Dirichlet definition of effective resistance for a connected terminal pair. -/
def unitEffectiveResistance (_connected : R.fullGraph.Reachable R.source R.target) : ℝ :=
  R.unitConductance⁻¹

theorem dirichletEnergy_nonneg (potential : Fin vertices → ℝ) : 0 ≤ R.dirichletEnergy potential :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem unitPotentialEnergies_nonempty : R.unitPotentialEnergies.Nonempty := by
  classical
  let potential : Fin vertices → ℝ := fun vertex => if vertex = R.source then 1 else 0
  refine ⟨R.dirichletEnergy potential, potential, ?_, ?_, rfl⟩
  · simp [potential]
  · simp [potential, Ne.symm R.terminals_distinct]

theorem unitPotentialEnergies_bddBelow : BddBelow R.unitPotentialEnergies := by
  refine ⟨0, ?_⟩
  rintro energy ⟨potential, _, _, rfl⟩
  exact R.dirichletEnergy_nonneg potential

theorem unitConductance_nonneg : 0 ≤ R.unitConductance := by
  apply le_csInf R.unitPotentialEnergies_nonempty
  rintro energy ⟨potential, _, _, rfl⟩
  exact R.dirichletEnergy_nonneg potential

theorem unitConductance_le_energy (potential : Fin vertices → ℝ)
    (hs : potential R.source = 1) (ht : potential R.target = 0) :
    R.unitConductance ≤ R.dirichletEnergy potential :=
  csInf_le R.unitPotentialEnergies_bddBelow ⟨potential, hs, ht, rfl⟩

theorem le_unitConductance (bound : ℝ)
    (hbound : ∀ potential : Fin vertices → ℝ, potential R.source = 1 → potential R.target = 0 →
      bound ≤ R.dirichletEnergy potential) : bound ≤ R.unitConductance := by
  apply le_csInf R.unitPotentialEnergies_nonempty
  rintro energy ⟨potential, hs, ht, rfl⟩
  exact hbound potential hs ht

theorem le_scaled_unitConductance (scale bound : ℝ) (hscale : 0 ≤ scale)
    (hbound : ∀ potential : Fin vertices → ℝ, potential R.source = 1 → potential R.target = 0 →
      bound ≤ scale * R.dirichletEnergy potential) : bound ≤ scale * R.unitConductance := by
  have hglb : IsGLB R.unitPotentialEnergies R.unitConductance :=
    isGLB_csInf R.unitPotentialEnergies_nonempty R.unitPotentialEnergies_bddBelow
  apply (hglb.mul_left hscale).2
  rintro value ⟨energy, ⟨potential, hs, ht, rfl⟩, rfl⟩
  exact hbound potential hs ht

theorem dirichletEnergy_affine (potential : Fin vertices → ℝ) (scale offset : ℝ) :
    R.dirichletEnergy (fun vertex => scale * potential vertex + offset) = scale ^ 2 * R.dirichletEnergy potential := by
  unfold dirichletEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem scaled_unitConductance_le_energy (potential : Fin vertices → ℝ) :
    R.unitConductance * (potential R.source - potential R.target) ^ 2 ≤ R.dirichletEnergy potential := by
  by_cases hd : potential R.source - potential R.target = 0
  · simpa only [hd, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero] using R.dirichletEnergy_nonneg potential
  · let normalized : Fin vertices → ℝ := fun vertex =>
      (potential vertex - potential R.target) / (potential R.source - potential R.target)
    have hs : normalized R.source = 1 := by simp [normalized, hd]
    have ht : normalized R.target = 0 := by simp [normalized]
    have heq : R.dirichletEnergy potential = (potential R.source - potential R.target) ^ 2 *
        R.dirichletEnergy normalized := by
      have hpoint : potential = fun vertex => (potential R.source - potential R.target) * normalized vertex + potential R.target := by
        funext vertex
        dsimp [normalized]
        field_simp [hd]
        <;> ring
      conv_lhs => rw [hpoint]
      exact R.dirichletEnergy_affine normalized _ _
    rw [heq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (R.unitConductance_le_energy normalized hs ht) (sq_nonneg _)

end
end Universality.FiniteNetwork

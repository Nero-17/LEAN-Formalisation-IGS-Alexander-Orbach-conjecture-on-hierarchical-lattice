import IGSIII34.Forms.AnchoredHilbert

set_option autoImplicit false
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit

variable {Carrier : Type*} {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)

theorem energyDomain_constant (constant : ℝ) :
    (fun _ : Carrier => constant) ∈ energyDomain endpoint conductance nonnegative := by
  refine ⟨0, ?_⟩
  rintro value ⟨depth, rfl⟩
  simp only [traceEnergy, finiteEnergy_constant, le_refl]

theorem limitingEnergy_add_constant (potential : Carrier → ℝ) (constant : ℝ) :
    limitingEnergy endpoint conductance (fun point => potential point + constant) =
      limitingEnergy endpoint conductance potential := by
  unfold limitingEnergy
  congr 1
  funext depth
  exact finiteEnergy_add_constant _ _ _ _

theorem limitingEnergy_sub_constant (potential : Carrier → ℝ) (constant : ℝ) :
    limitingEnergy endpoint conductance (fun point => potential point - constant) =
      limitingEnergy endpoint conductance potential := by
  simpa only [sub_eq_add_neg] using limitingEnergy_add_constant endpoint conductance potential (-constant)

def anchorSubtract (anchor : Carrier) (potential : energyDomain endpoint conductance nonnegative) :
    energyDomain endpoint conductance nonnegative :=
  ⟨fun point => potential.val point - potential.val anchor,
    (energyDomain endpoint conductance nonnegative).sub_mem potential.property
      (energyDomain_constant endpoint conductance nonnegative _)⟩

@[simp] theorem anchorSubtract_anchor (anchor : Carrier)
    (potential : energyDomain endpoint conductance nonnegative) :
    (anchorSubtract endpoint conductance nonnegative anchor potential).val anchor = 0 := by
  simp [anchorSubtract]

theorem anchorSubtract_energy (anchor : Carrier)
    (potential : energyDomain endpoint conductance nonnegative) :
    limitingEnergy endpoint conductance (anchorSubtract endpoint conductance nonnegative anchor potential).val =
      limitingEnergy endpoint conductance potential.val :=
  limitingEnergy_sub_constant endpoint conductance _ _

@[simp] theorem anchorSubtract_difference (anchor first second : Carrier)
    (potential : energyDomain endpoint conductance nonnegative) :
    (anchorSubtract endpoint conductance nonnegative anchor potential).val first -
      (anchorSubtract endpoint conductance nonnegative anchor potential).val second =
        potential.val first - potential.val second := by
  dsimp only [anchorSubtract]
  ring

end
end IGSIII34.Forms

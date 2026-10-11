import IGSIII34.ResistanceLimit.CompletionResistanceIdentity
import IGSIII34.Forms.EnergyAffine
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open IGSIII34.Forms

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)
variable (anchor : Carrier)

local instance completionAttainmentNormed : NormedAddCommGroup (energyDomain endpoint conductance nonnegative) :=
  anchoredNormedAddCommGroup endpoint conductance nonnegative monotone resistanceBound anchor
local instance completionAttainmentInner : InnerProductSpace ℝ (energyDomain endpoint conductance nonnegative) :=
  anchoredInnerProductSpace endpoint conductance nonnegative monotone resistanceBound anchor
local instance completionAttainmentComplete : CompleteSpace (energyDomain endpoint conductance nonnegative) :=
  anchored_completeSpace endpoint conductance nonnegative monotone resistanceBound anchor

include resistanceBound in
theorem completion_anchorSubtract_difference
    (potential : energyDomain endpoint conductance nonnegative)
    (first last : UniformSpace.Completion Carrier) :
    completionExtension endpoint conductance nonnegative
      (anchorSubtract endpoint conductance nonnegative anchor potential) first -
    completionExtension endpoint conductance nonnegative
      (anchorSubtract endpoint conductance nonnegative anchor potential) last =
      completionExtension endpoint conductance nonnegative potential first -
        completionExtension endpoint conductance nonnegative potential last := by
  have equality : completionExtension endpoint conductance nonnegative
      (anchorSubtract endpoint conductance nonnegative anchor potential) =
      (⟨fun point => completionExtension endpoint conductance nonnegative potential point - potential.val anchor,
        (completionExtension endpoint conductance nonnegative potential).continuous.sub continuous_const⟩ :
        C(UniformSpace.Completion Carrier, ℝ)) := by
    apply DFunLike.coe_injective
    apply (UniformSpace.Completion.denseRange_coe (α := Carrier)).equalizer
      (completionExtension endpoint conductance nonnegative
        (anchorSubtract endpoint conductance nonnegative anchor potential)).continuous
      ((completionExtension endpoint conductance nonnegative potential).continuous.sub continuous_const)
    funext point
    simp only [completionExtension_coe endpoint conductance nonnegative resistanceBound]
    rfl
  rw [equality]
  change (_ - _) - (_ - _) = _
  ring

def completionVoltageLinear (first last : UniformSpace.Completion Carrier) :
    energyDomain endpoint conductance nonnegative →ₗ[ℝ] ℝ where
  toFun potential := completionExtension endpoint conductance nonnegative potential first -
    completionExtension endpoint conductance nonnegative potential last
  map_add' firstPotential lastPotential := by
    change (completionExtensionLinear endpoint conductance nonnegative resistanceBound
      (firstPotential + lastPotential)) first -
      (completionExtensionLinear endpoint conductance nonnegative resistanceBound
        (firstPotential + lastPotential)) last = _
    rw [map_add]
    change (_ + _) - (_ + _) = _
    ring
  map_smul' scalar potential := by
    change (completionExtensionLinear endpoint conductance nonnegative resistanceBound (scalar • potential)) first -
      (completionExtensionLinear endpoint conductance nonnegative resistanceBound (scalar • potential)) last = _
    rw [map_smul]
    change scalar * _ - scalar * _ = scalar * (_ - _)
    ring

theorem completion_voltage_norm_bound
    (first last : UniformSpace.Completion Carrier)
    (potential : energyDomain endpoint conductance nonnegative) :
    ‖completionVoltageLinear endpoint conductance nonnegative resistanceBound first last potential‖ ≤
      Real.sqrt (dist first last) * ‖potential‖ := by
  have bound := completionExtension_resistance endpoint conductance nonnegative resistanceBound potential first last
  have square := anchored_norm_square endpoint conductance nonnegative monotone resistanceBound anchor potential
  dsimp only [anchoredSquare] at square
  have squareBound : (completionExtension endpoint conductance nonnegative potential first -
      completionExtension endpoint conductance nonnegative potential last) ^ 2 ≤
      (Real.sqrt (dist first last) * ‖potential‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (dist_nonneg : 0 ≤ dist first last), square]
    exact bound.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) dist_nonneg)
  change |completionExtension endpoint conductance nonnegative potential first -
    completionExtension endpoint conductance nonnegative potential last| ≤ _
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg potential))).mp
  simpa only [sq_abs] using squareBound

def completionVoltage (first last : UniformSpace.Completion Carrier) :
    energyDomain endpoint conductance nonnegative →L[ℝ] ℝ :=
  (completionVoltageLinear endpoint conductance nonnegative resistanceBound first last).mkContinuous
    (Real.sqrt (dist first last))
    (completion_voltage_norm_bound endpoint conductance nonnegative monotone resistanceBound anchor first last)

variable (attained : ∀ first last : Carrier, first ≠ last →
  ∃ potential : energyDomain endpoint conductance nonnegative,
    potential.val first = 0 ∧ potential.val last = 1 ∧
    limitingEnergy endpoint conductance potential.val = (dist first last)⁻¹)

/-- The completed evaluation difference has exactly the resistance operator norm. -/
theorem completionVoltage_norm_square (first last : UniformSpace.Completion Carrier) :
    ‖completionVoltage endpoint conductance nonnegative monotone resistanceBound anchor first last‖ ^ 2 =
      dist first last := by
  let voltage := completionVoltage endpoint conductance nonnegative monotone resistanceBound anchor first last
  have upper : ‖voltage‖ ≤ Real.sqrt (dist first last) :=
    (completionVoltageLinear endpoint conductance nonnegative resistanceBound first last).mkContinuous_norm_le
      (Real.sqrt_nonneg _) _
  apply le_antisymm
  · simpa only [Real.sq_sqrt (dist_nonneg : 0 ≤ dist first last)] using
      (sq_le_sq₀ (norm_nonneg voltage) (Real.sqrt_nonneg _)).mpr upper
  · apply completion_resistance_constant_optimal endpoint conductance nonnegative resistanceBound attained
      first last (‖voltage‖ ^ 2) (sq_nonneg _)
    intro potential
    have bound := voltage.le_opNorm (anchorSubtract endpoint conductance nonnegative anchor potential)
    have square := anchored_norm_square endpoint conductance nonnegative monotone resistanceBound anchor
      (anchorSubtract endpoint conductance nonnegative anchor potential)
    dsimp only [anchoredSquare] at square
    rw [anchorSubtract_anchor, zero_pow (by decide : 2 ≠ 0), add_zero,
      anchorSubtract_energy] at square
    change |completionExtension endpoint conductance nonnegative
      (anchorSubtract endpoint conductance nonnegative anchor potential) first -
      completionExtension endpoint conductance nonnegative
        (anchorSubtract endpoint conductance nonnegative anchor potential) last| ≤
        ‖voltage‖ * ‖anchorSubtract endpoint conductance nonnegative anchor potential‖ at bound
    rw [completion_anchorSubtract_difference endpoint conductance nonnegative resistanceBound anchor] at bound
    have squared := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg voltage)
      (norm_nonneg (anchorSubtract endpoint conductance nonnegative anchor potential)))).mpr bound
    simpa only [sq_abs, mul_pow, square] using squared

/-- Riesz representation gives an actual optimizer for every distinct completed pair. -/
theorem completion_resistance_attained
    (first last : UniformSpace.Completion Carrier) (distinct : first ≠ last) :
    ∃ potential : energyDomain endpoint conductance nonnegative,
      limitingEnergy endpoint conductance potential.val = dist first last ∧
      completionExtension endpoint conductance nonnegative potential first -
        completionExtension endpoint conductance nonnegative potential last = dist first last := by
  let voltage := completionVoltage endpoint conductance nonnegative monotone resistanceBound anchor first last
  let potential := (InnerProductSpace.toDual ℝ (energyDomain endpoint conductance nonnegative)).symm voltage
  have normEquality : ‖potential‖ = ‖voltage‖ :=
    (InnerProductSpace.toDual ℝ (energyDomain endpoint conductance nonnegative)).symm.norm_map voltage
  have normSquare : ‖potential‖ ^ 2 = dist first last := by
    rw [normEquality]
    exact completionVoltage_norm_square endpoint conductance nonnegative monotone resistanceBound anchor attained first last
  have voltageValue : voltage potential = dist first last := by
    have pairing := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
      (x := potential) (y := voltage)
    change inner ℝ potential potential = voltage potential at pairing
    rw [real_inner_self_eq_norm_sq] at pairing
    exact pairing.symm.trans normSquare
  have bound := completionExtension_resistance endpoint conductance nonnegative resistanceBound potential first last
  change (voltage potential) ^ 2 ≤ dist first last * limitingEnergy endpoint conductance potential.val at bound
  rw [voltageValue] at bound
  have square := anchored_norm_square endpoint conductance nonnegative monotone resistanceBound anchor potential
  dsimp only [anchoredSquare] at square
  have distancePositive := dist_pos.mpr distinct
  refine ⟨potential, ?_, voltageValue⟩
  nlinarith [sq_nonneg (potential.val anchor)]

end
end IGSIII34.ResistanceLimit

import IGSIII34.ResistanceLimit.LimitEnergy
import Mathlib.Analysis.InnerProductSpace.Defs

/-! The anchored inner product for a compatible finite trace system.
Only finite trace monotonicity and the resistance inequality are inputs.
Continuity of finite-energy functions is proved from that inequality.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)

include resistanceBound in
theorem finite_energy_continuous
    (potential : Carrier → ℝ) (finite : potential ∈ energyDomain endpoint conductance nonnegative) :
    Continuous potential := by
  have energyNonnegative := limitingEnergy_nonnegative endpoint conductance nonnegative finite
  apply continuous_iff_continuousAt.mpr
  intro point
  apply Metric.continuousAt_iff.mpr
  intro epsilon positive
  have denominatorPositive : 0 < limitingEnergy endpoint conductance potential + 1 := by linarith
  refine ⟨epsilon ^ 2 / (limitingEnergy endpoint conductance potential + 1),
    div_pos (sq_pos_of_pos positive) denominatorPositive, ?_⟩
  intro other close
  have bound := resistanceBound potential finite other point
  have multiplied := (mul_lt_mul_of_pos_right close denominatorPositive)
  rw [div_mul_cancel₀ _ denominatorPositive.ne'] at multiplied
  rw [Real.dist_eq]
  nlinarith [sq_abs (potential other - potential point), abs_nonneg (potential other - potential point),
    dist_nonneg (x := other) (y := point)]

def anchoredInner (anchor : Carrier)
    (first second : energyDomain endpoint conductance nonnegative) : ℝ :=
  limitingPairing endpoint conductance first.val second.val + first.val anchor * second.val anchor

@[reducible] def anchoredInnerCore (anchor : Carrier) :
    InnerProductSpace.Core ℝ (energyDomain endpoint conductance nonnegative) where
  inner := anchoredInner endpoint conductance nonnegative anchor
  conj_inner_symm first second := by
    change limitingPairing endpoint conductance second.val first.val + second.val anchor * first.val anchor = _
    rw [limitingPairing_comm endpoint conductance nonnegative monotone second.property first.property, mul_comm]
    rfl
  re_inner_nonneg first := by
    change 0 ≤ limitingPairing endpoint conductance first.val first.val + first.val anchor * first.val anchor
    rw [limitingPairing_self endpoint conductance nonnegative monotone first.property]
    exact add_nonneg (limitingEnergy_nonnegative endpoint conductance nonnegative first.property) (mul_self_nonneg _)
  add_left first second third := by
    change limitingPairing endpoint conductance (fun point => first.val point + second.val point) third.val +
        (first.val anchor + second.val anchor) * third.val anchor = _
    rw [limitingPairing_add_left endpoint conductance nonnegative monotone first.property second.property third.property]
    dsimp only [anchoredInner]
    ring
  smul_left first second scalar := by
    change limitingPairing endpoint conductance (fun point => scalar * first.val point) second.val +
        (scalar * first.val anchor) * second.val anchor = _
    rw [limitingPairing_smul_left endpoint conductance nonnegative monotone first.property second.property]
    dsimp only [anchoredInner]
    simp only [starRingEnd_apply, star_trivial]
    ring
  definite potential zero := by
    change limitingPairing endpoint conductance potential.val potential.val + potential.val anchor * potential.val anchor = 0 at zero
    rw [limitingPairing_self endpoint conductance nonnegative monotone potential.property] at zero
    have energyNonnegative := limitingEnergy_nonnegative endpoint conductance nonnegative potential.property
    have anchorZero : potential.val anchor = 0 := by nlinarith [sq_nonneg (potential.val anchor)]
    have energyZero : limitingEnergy endpoint conductance potential.val = 0 := by rw [anchorZero] at zero; linarith
    apply Subtype.ext
    funext point
    have bound := resistanceBound potential.val potential.property point anchor
    rw [anchorZero, energyZero] at bound
    change potential.val point = 0
    nlinarith [sq_nonneg (potential.val point)]

end
end IGSIII34.Forms

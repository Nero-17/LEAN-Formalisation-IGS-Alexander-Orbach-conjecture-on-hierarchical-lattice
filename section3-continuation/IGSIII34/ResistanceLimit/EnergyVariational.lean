import IGSIII34.ResistanceLimit.LimitEnergy

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section

variable {Carrier : Type*} {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (monotone : ∀ potential, Monotone (fun depth => traceEnergy endpoint conductance depth potential))

theorem limitingEnergy_add_identity (first second : Carrier → ℝ) :
    limitingEnergy endpoint conductance (fun point => first point + second point) =
      limitingEnergy endpoint conductance first + limitingEnergy endpoint conductance second +
        2 * limitingPairing endpoint conductance first second := by
  unfold limitingPairing
  ring

include monotone in
theorem limitingPairing_smul_right
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative) (scalar : ℝ) :
    limitingPairing endpoint conductance first (fun point => scalar * second point) =
      scalar * limitingPairing endpoint conductance first second := by
  have scaledFinite : (fun point => scalar * second point) ∈ energyDomain endpoint conductance nonnegative :=
    (energyDomain endpoint conductance nonnegative).smul_mem scalar secondFinite
  rw [limitingPairing_comm endpoint conductance nonnegative monotone firstFinite
    scaledFinite,
    limitingPairing_smul_left endpoint conductance nonnegative monotone secondFinite firstFinite,
    limitingPairing_comm endpoint conductance nonnegative monotone secondFinite firstFinite]

include monotone in
theorem limitingEnergy_smul_identity
    {potential : Carrier → ℝ} (finite : potential ∈ energyDomain endpoint conductance nonnegative) (scalar : ℝ) :
    limitingEnergy endpoint conductance (fun point => scalar * potential point) =
      scalar ^ 2 * limitingEnergy endpoint conductance potential := by
  have scaledFinite : (fun point => scalar * potential point) ∈ energyDomain endpoint conductance nonnegative :=
    (energyDomain endpoint conductance nonnegative).smul_mem scalar finite
  rw [← limitingPairing_self endpoint conductance nonnegative monotone scaledFinite,
    limitingPairing_smul_left endpoint conductance nonnegative monotone finite scaledFinite,
    limitingPairing_smul_right endpoint conductance nonnegative monotone finite finite,
    limitingPairing_self endpoint conductance nonnegative monotone finite]
  ring

theorem linear_eq_zero_of_nonnegative_quadratic (quadratic linear : ℝ)
    (quadraticNonnegative : 0 ≤ quadratic)
    (nonnegative : ∀ scalar : ℝ, 0 ≤ scalar ^ 2 * quadratic + 2 * scalar * linear) : linear = 0 := by
  have denominatorPositive : 0 < quadratic + 1 := by linarith
  have bound := nonnegative (-linear / (quadratic + 1))
  have identity : (-linear / (quadratic + 1)) ^ 2 * quadratic +
      2 * (-linear / (quadratic + 1)) * linear =
      -(linear ^ 2 * (quadratic + 2)) / (quadratic + 1) ^ 2 := by
    field_simp [denominatorPositive.ne']
    ring
  rw [identity] at bound
  have numerator := (le_div_iff₀ (sq_pos_of_pos denominatorPositive)).mp bound
  have squareNonpositive : linear ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ (show 0 < quadratic + 2 by linarith)).mp
      (by simpa only [zero_mul, mul_zero, mul_comm] using neg_nonneg.mp (show 0 ≤ -(linear ^ 2 * (quadratic + 2)) by simpa using numerator))
  exact sq_eq_zero_iff.mp (le_antisymm squareNonpositive (sq_nonneg _))

include monotone in
theorem limitingPairing_eq_zero_of_minimal
    {first second : Carrier → ℝ}
    (firstFinite : first ∈ energyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ energyDomain endpoint conductance nonnegative)
    (minimal : ∀ scalar : ℝ,
      limitingEnergy endpoint conductance first ≤
        limitingEnergy endpoint conductance (fun point => first point + scalar * second point)) :
    limitingPairing endpoint conductance first second = 0 := by
  apply linear_eq_zero_of_nonnegative_quadratic
    (limitingEnergy endpoint conductance second) (limitingPairing endpoint conductance first second)
    (limitingEnergy_nonnegative endpoint conductance nonnegative secondFinite)
  intro scalar
  have bound := minimal scalar
  rw [limitingEnergy_add_identity,
    limitingEnergy_smul_identity endpoint conductance nonnegative monotone secondFinite scalar,
    limitingPairing_smul_right endpoint conductance nonnegative monotone firstFinite secondFinite scalar] at bound
  nlinarith

end
end IGSIII34.ResistanceLimit

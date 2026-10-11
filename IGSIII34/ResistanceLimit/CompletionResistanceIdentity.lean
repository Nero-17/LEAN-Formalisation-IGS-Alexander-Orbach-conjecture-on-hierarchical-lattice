import IGSIII34.Forms.CompletionRegularityCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open IGSIII34.Forms Filter
open scoped _root_.Topology

private theorem three_gap_square (first middle last parameter : ℝ) (positive : 0 < parameter) :
    (first + middle + last) ^ 2 ≤ (1 + parameter) * middle ^ 2 +
      2 * (1 + parameter⁻¹) * (first ^ 2 + last ^ 2) := by
  have identity : parameter * ((1 + parameter) * middle ^ 2 +
      (1 + parameter⁻¹) * (first + last) ^ 2 - (first + middle + last) ^ 2) =
        (parameter * middle - (first + last)) ^ 2 := by
    field_simp
    <;> ring
  have young : (first + middle + last) ^ 2 ≤ (1 + parameter) * middle ^ 2 +
      (1 + parameter⁻¹) * (first + last) ^ 2 := by
    nlinarith [sq_nonneg (parameter * middle - (first + last))]
  have inverseNonnegative : 0 ≤ parameter⁻¹ := inv_nonneg.mpr positive.le
  have adjacent : (first + last) ^ 2 ≤ 2 * (first ^ 2 + last ^ 2) := by
    nlinarith [sq_nonneg (first - last)]
  exact young.trans (by nlinarith [mul_le_mul_of_nonneg_left adjacent (show 0 ≤ 1 + parameter⁻¹ by linarith)])

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)
variable (attained : ∀ first last : Carrier, first ≠ last →
  ∃ potential : energyDomain endpoint conductance nonnegative,
    potential.val first = 0 ∧ potential.val last = 1 ∧
    limitingEnergy endpoint conductance potential.val = (dist first last)⁻¹)

include resistanceBound attained in
/-- The completion distance is the least possible constant in its energy
inequality. Approximation uses genuine skeleton minimizers. -/
theorem completion_resistance_constant_optimal
    (first last : UniformSpace.Completion Carrier) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (energyBound : ∀ potential : energyDomain endpoint conductance nonnegative,
      (completionExtension endpoint conductance nonnegative potential first -
        completionExtension endpoint conductance nonnegative potential last) ^ 2 ≤
          bound * limitingEnergy endpoint conductance potential.val) :
    dist first last ≤ bound := by
  apply le_of_forall_pos_le_add
  intro tolerance tolerancePositive
  let parameter := tolerance / (2 * (bound + 1))
  have parameterPositive : 0 < parameter := div_pos tolerancePositive (by positivity)
  let coefficient := 2 * (1 + parameter⁻¹)
  have coefficientPositive : 0 < coefficient := by dsimp [coefficient]; positivity
  let radius := tolerance / (4 * (coefficient + 1))
  have radiusPositive : 0 < radius := div_pos tolerancePositive (by positivity)
  obtain ⟨firstVertex, firstClose⟩ := (UniformSpace.Completion.denseRange_coe (α := Carrier)).exists_dist_lt first radiusPositive
  obtain ⟨lastVertex, lastClose⟩ := (UniformSpace.Completion.denseRange_coe (α := Carrier)).exists_dist_lt last radiusPositive
  have finiteBound : dist firstVertex lastVertex ≤ (1 + parameter) * bound +
      coefficient * (dist first firstVertex + dist last lastVertex) := by
    by_cases equal : firstVertex = lastVertex
    · rw [equal, dist_self]
      positivity
    obtain ⟨potential, firstValue, lastValue, energy⟩ := attained firstVertex lastVertex equal
    have energyPositive : 0 < limitingEnergy endpoint conductance potential.val := by
      rw [energy]
      exact inv_pos.mpr (dist_pos.mpr equal)
    have firstBound := completionExtension_resistance endpoint conductance nonnegative resistanceBound potential first firstVertex
    have lastBound := completionExtension_resistance endpoint conductance nonnegative resistanceBound potential last lastVertex
    rw [completionExtension_coe endpoint conductance nonnegative resistanceBound, firstValue] at firstBound
    rw [completionExtension_coe endpoint conductance nonnegative resistanceBound, lastValue] at lastBound
    have middleBound := energyBound potential
    have combined := three_gap_square
      (-completionExtension endpoint conductance nonnegative potential first)
      (completionExtension endpoint conductance nonnegative potential first -
        completionExtension endpoint conductance nonnegative potential last)
      (completionExtension endpoint conductance nonnegative potential last - 1) parameter parameterPositive
    have voltage : (-completionExtension endpoint conductance nonnegative potential first +
        (completionExtension endpoint conductance nonnegative potential first -
          completionExtension endpoint conductance nonnegative potential last) +
        (completionExtension endpoint conductance nonnegative potential last - 1)) ^ 2 = 1 := by ring
    rw [voltage] at combined
    have coefficientNonnegative := coefficientPositive.le
    have parameterFactor : 0 ≤ 1 + parameter := by positivity
    have sumBound := add_le_add firstBound lastBound
    have middleScaled := mul_le_mul_of_nonneg_left middleBound parameterFactor
    have sidesScaled := mul_le_mul_of_nonneg_left sumBound coefficientNonnegative
    have oneBound : 1 ≤ ((1 + parameter) * bound +
        coefficient * (dist first firstVertex + dist last lastVertex)) *
          limitingEnergy endpoint conductance potential.val := by
      dsimp [coefficient] at sidesScaled ⊢
      nlinarith [combined]
    rw [energy] at oneBound
    have distancePositive := dist_pos.mpr equal
    have cancelled := (le_div_iff₀ distancePositive).mp (by
      simpa only [← div_eq_mul_inv] using oneBound)
    simpa only [one_mul] using cancelled
  have triangle := dist_triangle first (firstVertex : UniformSpace.Completion Carrier) last
  have otherTriangle := dist_triangle (firstVertex : UniformSpace.Completion Carrier)
    (lastVertex : UniformSpace.Completion Carrier) last
  rw [UniformSpace.Completion.dist_eq, dist_comm (lastVertex : UniformSpace.Completion Carrier) last] at otherTriangle
  have radiusIdentity : 4 * (coefficient + 1) * radius = tolerance := by
    dsimp [radius]
    field_simp
  have parameterIdentity : 2 * (bound + 1) * parameter = tolerance := by
    dsimp [parameter]
    field_simp
  nlinarith [mul_nonneg parameterPositive.le (show 0 ≤ bound + 1 by positivity)]

end
end IGSIII34.ResistanceLimit

import IGSIII34.ResistanceLimit.CompletionResistanceIdentity

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open IGSIII34.Forms

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)

def completionVariationalResistance (first last : UniformSpace.Completion Carrier) : ℝ :=
  sSup (insert 0 {ratio : ℝ | ∃ potential : energyDomain endpoint conductance nonnegative,
    0 < limitingEnergy endpoint conductance potential.val ∧
    ratio = (completionExtension endpoint conductance nonnegative potential first -
      completionExtension endpoint conductance nonnegative potential last) ^ 2 /
        limitingEnergy endpoint conductance potential.val})

variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)
variable (attained : ∀ first last : Carrier, first ≠ last →
  ∃ potential : energyDomain endpoint conductance nonnegative,
    potential.val first = 0 ∧ potential.val last = 1 ∧
    limitingEnergy endpoint conductance potential.val = (dist first last)⁻¹)

include resistanceBound attained in
/-- On every pair in the completion, the metric is exactly the variational
resistance of the continuous finite-energy extension domain. -/
theorem completionVariationalResistance_eq_dist (first last : UniformSpace.Completion Carrier) :
    completionVariationalResistance endpoint conductance nonnegative first last = dist first last := by
  have ratioBound : ∀ ratio ∈ insert 0 {ratio : ℝ | ∃ potential : energyDomain endpoint conductance nonnegative,
      0 < limitingEnergy endpoint conductance potential.val ∧
      ratio = (completionExtension endpoint conductance nonnegative potential first -
        completionExtension endpoint conductance nonnegative potential last) ^ 2 /
          limitingEnergy endpoint conductance potential.val}, ratio ≤ dist first last := by
    intro ratio membership
    rcases membership with zero | ⟨potential, energyPositive, ratioEquality⟩
    · simpa only [zero] using (dist_nonneg : 0 ≤ dist first last)
    · rw [ratioEquality]
      exact (div_le_iff₀ energyPositive).mpr
        (completionExtension_resistance endpoint conductance nonnegative resistanceBound potential first last)
  have bounded : BddAbove (insert 0 {ratio : ℝ | ∃ potential : energyDomain endpoint conductance nonnegative,
      0 < limitingEnergy endpoint conductance potential.val ∧
      ratio = (completionExtension endpoint conductance nonnegative potential first -
        completionExtension endpoint conductance nonnegative potential last) ^ 2 /
          limitingEnergy endpoint conductance potential.val}) := ⟨dist first last, ratioBound⟩
  have nonempty : (insert 0 {ratio : ℝ | ∃ potential : energyDomain endpoint conductance nonnegative,
      0 < limitingEnergy endpoint conductance potential.val ∧
      ratio = (completionExtension endpoint conductance nonnegative potential first -
        completionExtension endpoint conductance nonnegative potential last) ^ 2 /
          limitingEnergy endpoint conductance potential.val}).Nonempty := ⟨0, Set.mem_insert _ _⟩
  apply le_antisymm
  · exact csSup_le nonempty ratioBound
  · have resistanceNonnegative : 0 ≤ completionVariationalResistance endpoint conductance nonnegative first last :=
      le_csSup bounded (Set.mem_insert _ _)
    apply completion_resistance_constant_optimal endpoint conductance nonnegative resistanceBound attained
      first last _ resistanceNonnegative
    intro potential
    have energyNonnegative := limitingEnergy_nonnegative endpoint conductance nonnegative potential.property
    by_cases energyPositive : 0 < limitingEnergy endpoint conductance potential.val
    · have ratioBelow : (completionExtension endpoint conductance nonnegative potential first -
          completionExtension endpoint conductance nonnegative potential last) ^ 2 /
          limitingEnergy endpoint conductance potential.val ≤
            completionVariationalResistance endpoint conductance nonnegative first last := by
        apply le_csSup bounded
        exact Set.mem_insert_of_mem _ ⟨potential, energyPositive, rfl⟩
      exact (div_le_iff₀ energyPositive).mp ratioBelow
    · have energyZero : limitingEnergy endpoint conductance potential.val = 0 := by linarith
      have zeroVoltage := completionExtension_resistance endpoint conductance nonnegative resistanceBound potential first last
      simpa only [energyZero, mul_zero] using zeroVoltage

end
end IGSIII34.ResistanceLimit

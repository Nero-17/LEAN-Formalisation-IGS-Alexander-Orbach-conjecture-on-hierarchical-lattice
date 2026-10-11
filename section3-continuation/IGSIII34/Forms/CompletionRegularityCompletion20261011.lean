import IGSIII34.Forms.CompletionDomainCompletion20261011

/-! Dense finite-energy functions on a compact resistance completion. The
separation argument uses actual skeleton resistance minimizers, and not an
assumed separation property of the completion. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

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
theorem completionEnergyDomain_separates
    (first last : UniformSpace.Completion Carrier) (distinct : first ≠ last) :
    ∃ potential ∈ completionEnergyDomain endpoint conductance nonnegative,
      potential first ≠ potential last := by
  have distancePositive : 0 < dist first last := dist_pos.mpr distinct
  obtain ⟨firstVertex, firstClose⟩ := (UniformSpace.Completion.denseRange_coe (α := Carrier)).exists_dist_lt
    first (show 0 < dist first last / 100 by positivity)
  obtain ⟨lastVertex, lastClose⟩ := (UniformSpace.Completion.denseRange_coe (α := Carrier)).exists_dist_lt
    last (show 0 < dist first last / 100 by positivity)
  have firstTriangle := dist_triangle first (firstVertex : UniformSpace.Completion Carrier) last
  have lastTriangle := dist_triangle (firstVertex : UniformSpace.Completion Carrier)
      (lastVertex : UniformSpace.Completion Carrier) last
  rw [UniformSpace.Completion.dist_eq, dist_comm (lastVertex : UniformSpace.Completion Carrier) last] at lastTriangle
  have triangle : dist first last ≤ dist first (firstVertex : UniformSpace.Completion Carrier) +
      dist firstVertex lastVertex + dist last (lastVertex : UniformSpace.Completion Carrier) := by linarith
  have vertexDistancePositive : 0 < dist firstVertex lastVertex := by linarith
  obtain ⟨potential, firstValue, lastValue, energy⟩ := attained firstVertex lastVertex
    (dist_pos.mp vertexDistancePositive)
  refine ⟨completionExtension endpoint conductance nonnegative potential, ?_, ?_⟩
  · change (fun point : Carrier => completionExtension endpoint conductance nonnegative potential point) ∈
      energyDomain endpoint conductance nonnegative
    simpa only [completionExtension_coe endpoint conductance nonnegative resistanceBound] using potential.property
  · have firstBound := completionExtension_resistance endpoint conductance nonnegative resistanceBound
      potential first (firstVertex : UniformSpace.Completion Carrier)
    have lastBound := completionExtension_resistance endpoint conductance nonnegative resistanceBound
      potential last (lastVertex : UniformSpace.Completion Carrier)
    rw [completionExtension_coe endpoint conductance nonnegative resistanceBound, firstValue, energy,
      sub_zero] at firstBound
    rw [completionExtension_coe endpoint conductance nonnegative resistanceBound, lastValue, energy] at lastBound
    have firstSmall : dist first (firstVertex : UniformSpace.Completion Carrier) * (dist firstVertex lastVertex)⁻¹ < 1 / 16 := by
      rw [← div_eq_mul_inv, div_lt_iff₀ vertexDistancePositive]
      linarith
    have lastSmall : dist last (lastVertex : UniformSpace.Completion Carrier) * (dist firstVertex lastVertex)⁻¹ < 1 / 16 := by
      rw [← div_eq_mul_inv, div_lt_iff₀ vertexDistancePositive]
      linarith
    intro equal
    rw [equal] at firstBound
    nlinarith [firstBound.trans_lt firstSmall, lastBound.trans_lt lastSmall,
      sq_nonneg (completionExtension endpoint conductance nonnegative potential last - (1 / 2 : ℝ))]

include resistanceBound attained in
theorem completionEnergyDomain_separates_strongly :
    (completionEnergyDomain endpoint conductance nonnegative :
      Set C(UniformSpace.Completion Carrier, ℝ)).SeparatesPointsStrongly := by
  intro values first last
  by_cases equal : first = last
  · subst last
    exact ⟨ContinuousMap.const _ (values first),
      completionEnergyDomain_constant endpoint conductance nonnegative _, rfl, rfl⟩
  obtain ⟨potential, finite, different⟩ := completionEnergyDomain_separates endpoint conductance
    nonnegative resistanceBound attained first last equal
  let transformed : C(UniformSpace.Completion Carrier, ℝ) :=
    ((values last - values first) * (potential first - potential last)⁻¹) •
      (ContinuousMap.const _ (potential first) - potential) + ContinuousMap.const _ (values first)
  refine ⟨transformed, ?_, ?_, ?_⟩
  · exact (completionEnergyDomain endpoint conductance nonnegative).add_mem
      ((completionEnergyDomain endpoint conductance nonnegative).smul_mem _
        ((completionEnergyDomain endpoint conductance nonnegative).sub_mem
          (completionEnergyDomain_constant endpoint conductance nonnegative _) finite))
      (completionEnergyDomain_constant endpoint conductance nonnegative _)
  · simp [transformed]
  · simp [transformed, inv_mul_cancel_right₀ (sub_ne_zero.mpr different)]

include resistanceBound attained in
theorem completionEnergyDomain_dense [CompactSpace (UniformSpace.Completion Carrier)] :
    Dense (completionEnergyDomain endpoint conductance nonnegative :
      Set C(UniformSpace.Completion Carrier, ℝ)) := by
  apply dense_iff_closure_eq.mpr
  exact ContinuousMap.sublattice_closure_eq_top
    (completionEnergyDomain endpoint conductance nonnegative : Set C(UniformSpace.Completion Carrier, ℝ))
    ⟨0, (completionEnergyDomain endpoint conductance nonnegative).zero_mem⟩
    (fun _ firstFinite _ secondFinite => completionEnergyDomain_inf endpoint conductance nonnegative firstFinite secondFinite)
    (fun _ firstFinite _ secondFinite => completionEnergyDomain_sup endpoint conductance nonnegative firstFinite secondFinite)
    (completionEnergyDomain_separates_strongly endpoint conductance nonnegative resistanceBound attained)

end
end IGSIII34.Forms

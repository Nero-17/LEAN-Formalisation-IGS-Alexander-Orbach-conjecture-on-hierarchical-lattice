import IGSIII34.Spectral.MassMoments
import Universality.Percolation.CoarseRootMoments

/-! Positive integer moments for all actual oriented mass limits, including
the two jointly coupled sides of a noncrossing cell. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter Matrix
open scoped Topology ENNReal

theorem nonconnected_history_mass_moment_bound
    {rule : Rule} (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (parent : OrientedState) (nonconnected : parent ≠ .connected)
    (power : ℕ) (bound : ℝ)
    (boundaryBounds : ∀ depth, (∫ path,
      (Rule.ConfigurationHistory.vertexMass rule .both depth path / growth ^ depth) ^ power
      ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint false) ≤ bound) :
    ∀ depth, (∫ path,
      (((rule.generation depth).network.internalStateMass parent
        (Rule.ConfigurationHistory.latest rule depth (path depth)) : ℝ) / growth ^ depth) ^ power
      ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened) ≤ bound := by
  have parentClosed : parent.massOpened = false := by
    cases parent <;> simp_all [OrientedState.massOpened]
  rw [parentClosed]
  intro depth
  have firstIntegrable := Rule.ConfigurationHistory.memLp_infiniteLaw_observable rule p positive belowOne
    fixedPoint false depth (fun history =>
      (((rule.generation depth).network.internalStateMass parent
        (Rule.ConfigurationHistory.latest rule depth history) : ℝ) / growth ^ depth) ^ power) 1
      |>.integrable le_rfl
  have secondIntegrable := Rule.ConfigurationHistory.memLp_infiniteLaw_observable rule p positive belowOne
    fixedPoint false depth (fun history =>
      (((rule.generation depth).network.internalSelectedMass true true
        (Rule.ConfigurationHistory.latest rule depth history) : ℝ) / growth ^ depth) ^ power) 1
      |>.integrable le_rfl
  apply le_trans (integral_mono firstIntegrable secondIntegrable ?_) (boundaryBounds depth)
  intro path
  apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (pow_pos growthPositive depth).le)
  apply div_le_div_of_nonneg_right _ (pow_pos growthPositive depth).le
  exact_mod_cast (rule.generation depth).network.internalSelectedMass_le_boundary
    parent.sourceSelected parent.targetSelected _

theorem actual_oriented_history_limit_uniform_nat_moment
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (power : ℕ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (parent : OrientedState)
      (limit : (Π depth, rule.ConfigurationHistory depth) → ℝ),
      (∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened,
        Tendsto (fun depth => ((rule.generation depth).network.internalStateMass parent
          (Rule.ConfigurationHistory.latest rule depth (path depth)) : ℝ) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 (limit path))) →
      (∫⁻ path, ENNReal.ofReal (limit path) ^ power
        ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened) ≤
          ENNReal.ofReal bound := by
  obtain ⟨bound, boundPositive, bounds⟩ := classicalRule.infinite_normalized_vertex_moment_bounds
    p positive belowOne fixedPoint power
  have growthPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨bound, boundPositive, ?_⟩
  intro parent limit convergence
  by_cases connected : parent = .connected
  · subst parent
    have connectedConvergence : ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true,
        Tendsto (fun depth => Rule.ConfigurationHistory.vertexMass rule .connected depth path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 (limit path)) := by
      filter_upwards [convergence, Rule.ConfigurationHistory.infiniteLaw_crosses rule p positive belowOne fixedPoint true]
        with path converges crosses
      convert converges using 1
      funext depth
      simp only [Rule.ConfigurationHistory.vertexMass, internalStateMass,
        OrientedState.sourceSelected, OrientedState.targetSelected,
        show (LiveState.connected == LiveState.both) = false from rfl]
      rw [(rule.generation depth).network.internalSelectedMass_connected _ (crosses depth)]
    apply limiting_nat_moment_le _
      (fun depth path => Rule.ConfigurationHistory.vertexMass rule .connected depth path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
      limit power bound
    · intro depth path
      exact div_nonneg (Nat.cast_nonneg _) (pow_pos growthPositive depth).le
    · intro depth
      exact Rule.ConfigurationHistory.memLp_infiniteLaw_observable rule p positive belowOne fixedPoint
        true depth (fun history =>
          (((rule.generation depth).network.internalSelectedMass true false
            (Rule.ConfigurationHistory.latest rule depth history) : ℝ) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth) ^ power) 1
        |>.integrable le_rfl
    · intro depth
      exact bounds depth .connected
    · exact connectedConvergence
  · apply limiting_nat_moment_le _
      (fun depth path => ((rule.generation depth).network.internalStateMass parent
        (Rule.ConfigurationHistory.latest rule depth (path depth)) : ℝ) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
      limit power bound
    · intro depth path
      exact div_nonneg (Nat.cast_nonneg _) (pow_pos growthPositive depth).le
    · intro depth
      exact Rule.ConfigurationHistory.memLp_infiniteLaw_observable rule p positive belowOne fixedPoint
        parent.massOpened depth (fun history =>
          (((rule.generation depth).network.internalStateMass parent
            (Rule.ConfigurationHistory.latest rule depth history) : ℝ) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth) ^ power) 1
        |>.integrable le_rfl
    · exact nonconnected_history_mass_moment_bound p positive belowOne fixedPoint _ growthPositive parent
        connected power bound (fun depth => bounds depth .both)
    · exact convergence

end
end IGSIII34.Spectral

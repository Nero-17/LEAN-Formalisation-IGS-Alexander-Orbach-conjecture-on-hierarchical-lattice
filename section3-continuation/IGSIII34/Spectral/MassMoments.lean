import IGSIII.Mass.CylinderMassLimits
import Universality.Percolation.InfiniteMassMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Fatou transfer of the actual finite-cluster moment bounds to the
first-birth mass limits. No inverse mass moment is used. -/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter Matrix
open scoped Topology ENNReal

theorem limiting_nat_moment_le
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (sequence : ℕ → Sample → ℝ) (limit : Sample → ℝ) (power : ℕ) (bound : ℝ)
    (nonnegative : ∀ depth sample, 0 ≤ sequence depth sample)
    (integrable : ∀ depth, Integrable (fun sample => sequence depth sample ^ power) measure)
    (momentBound : ∀ depth, (∫ sample, sequence depth sample ^ power ∂measure) ≤ bound)
    (convergence : ∀ᵐ sample ∂measure,
      Tendsto (fun depth => sequence depth sample) atTop (𝓝 (limit sample))) :
    (∫⁻ sample, ENNReal.ofReal (limit sample) ^ power ∂measure) ≤ ENNReal.ofReal bound := by
  have momentConvergence : ∀ᵐ sample ∂measure,
      Tendsto (fun depth => ENNReal.ofReal (sequence depth sample) ^ power) atTop
        (𝓝 (ENNReal.ofReal (limit sample) ^ power)) := by
    filter_upwards [convergence] with sample converges
    exact (ENNReal.continuous_pow power).continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp converges)
  have measurable : ∀ depth, AEMeasurable
      (fun sample => ENNReal.ofReal (sequence depth sample) ^ power) measure := by
    intro depth
    have equality : (fun sample => ENNReal.ofReal (sequence depth sample) ^ power) =
        (fun sample => ENNReal.ofReal (sequence depth sample ^ power)) := by
      funext sample
      exact (ENNReal.ofReal_pow (nonnegative depth sample) power).symm
    rw [equality]
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (integrable depth).aestronglyMeasurable.aemeasurable
  have integralBound : ∀ depth,
      (∫⁻ sample, ENNReal.ofReal (sequence depth sample) ^ power ∂measure) ≤ ENNReal.ofReal bound := by
    intro depth
    have equality := ofReal_integral_eq_lintegral_ofReal (integrable depth)
      (Filter.Eventually.of_forall (fun sample => pow_nonneg (nonnegative depth sample) power))
    simp_rw [ENNReal.ofReal_pow (nonnegative depth _) power] at equality
    rw [← equality]
    exact ENNReal.ofReal_le_ofReal (momentBound depth)
  calc
    _ = ∫⁻ sample, liminf (fun depth => ENNReal.ofReal (sequence depth sample) ^ power) atTop ∂measure :=
      lintegral_congr_ae (momentConvergence.mono (fun _ converges => converges.liminf_eq.symm))
    _ ≤ liminf (fun depth => ∫⁻ sample, ENNReal.ofReal (sequence depth sample) ^ power ∂measure) atTop :=
      lintegral_liminf_le' measurable
    _ ≤ ENNReal.ofReal bound := liminf_le_of_frequently_le' (Frequently.of_forall integralBound)

theorem actual_history_mass_limit_uniform_nat_moment
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (power : ℕ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (state : LiveState)
      (limit : (Π depth, rule.ConfigurationHistory depth) → ℝ),
      (∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected),
        Tendsto (fun depth => Rule.ConfigurationHistory.vertexMass rule state depth path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 (limit path))) →
      (∫⁻ path, ENNReal.ofReal (limit path) ^ power
        ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)) ≤
          ENNReal.ofReal bound := by
  obtain ⟨bound, boundPositive, bounds⟩ := classicalRule.infinite_normalized_vertex_moment_bounds
    p positive belowOne fixedPoint power
  have growthPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨bound, boundPositive, ?_⟩
  intro state limit convergence
  apply limiting_nat_moment_le _
    (fun depth path => Rule.ConfigurationHistory.vertexMass rule state depth path /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
    limit power bound
  · intro depth path
    exact div_nonneg (Nat.cast_nonneg _) (pow_pos growthPositive depth).le
  · intro depth
    exact Rule.ConfigurationHistory.memLp_infiniteLaw_observable rule p positive belowOne fixedPoint
      (state == .connected) depth
      (fun history => (((rule.generation depth).network.internalSelectedMass true (state == .both)
        (Rule.ConfigurationHistory.latest rule depth history) : ℝ) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth) ^ power) 1
      |>.integrable le_rfl
  · intro depth
    exact bounds depth state
  · exact convergence

end
end IGSIII34.Spectral

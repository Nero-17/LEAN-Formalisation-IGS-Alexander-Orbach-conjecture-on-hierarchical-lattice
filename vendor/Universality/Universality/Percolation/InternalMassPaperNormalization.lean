import Universality.Probability.LocalLimitDepthShift
import Universality.Probability.DensityDivision
namespace Universality.Rule
noncomputable section
open FiniteNetwork MeasureTheory Filter
open scoped Topology ContDiff

/-- Literal manuscript-depth normalization: generation n is paper depth n+1.
Both the random-variable law and the uniform lattice density are rescaled,
with no appeal to an unspecified multiplicative constant. -/
theorem Classical.internal_mass_paper_normalization {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ,
      ∃ density : LiveState → ℝ → ℝ,
      (∀ state, (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map
        (limit state) = volume.withDensity (fun x => ENNReal.ofReal (density state x))) ∧
      (∀ state, MemLp (fun path => limit state path /
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) 2
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) ∧
      (∀ state, ContDiff ℝ ∞ (fun x =>
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
          density state ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * x))) ∧
      (∀ state x, 0 ≤ (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
        density state ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * x)) ∧
      (∀ state, Integrable (fun x =>
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
          density state ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * x))) ∧
      (∀ state, (∫ x, (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
          density state ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * x)) = 1) ∧
      (∀ state, (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map
        (fun path => limit state path / (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) =
        volume.withDensity (fun x => ENNReal.ofReal
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
            density state ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * x)))) ∧
      (∀ state x, x < 0 →
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
          density state ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * x) = 0) ∧
      (∀ x : ℝ, 0 < x → 0 <
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
          density .single ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * x)) ∧
      ∀ state error, 0 < error → ∀ᶠ n : ℕ in atTop, ∀ size : ℤ,
        |((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1) *
          (rule.generation n).network.conditionalInternalIntegerMassProbability p
            (state == .connected) true (state == .both) size -
          (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
            density state ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal *
              ((size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1)))| < error := by
  obtain ⟨limit, density, hmem, hsmooth, hnonneg, hintegrable, hintegral, hlaw,
    hnegative, hpositive, hllt⟩ := h.internal_mass_smooth_positive_integer_local_limit p hp hp' hfixed
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hproperties (state : LiveState) := depth_shift_density_properties _ hradius (density state)
    (hsmooth state) (hnonneg state) (hintegrable state) (hintegral state) (hnegative state)
  refine ⟨limit, density, hlaw, ?_, fun state => (hproperties state).1,
    fun state => (hproperties state).2.1, fun state => (hproperties state).2.2.1,
    fun state => (hproperties state).2.2.2.1, ?_, fun state => (hproperties state).2.2.2.2, ?_, ?_⟩
  · intro state
    simpa only [div_eq_mul_inv, mul_comm] using (hmem state).const_mul
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)⁻¹
  · intro state
    exact randomVariable_div_density _ (limit state)
      (hmem state).aestronglyMeasurable.aemeasurable _ hradius (density state)
      (hsmooth state).continuous.measurable (hlaw state)
  · intro x hx
    exact mul_pos hradius (hpositive _ (mul_pos hradius hx))
  · intro state
    exact uniform_local_limit_depth_shift _ hradius
      (fun n size => (rule.generation n).network.conditionalInternalIntegerMassProbability p
        (state == .connected) true (state == .both) size) (density state) (hllt state)

end
end Universality.Rule

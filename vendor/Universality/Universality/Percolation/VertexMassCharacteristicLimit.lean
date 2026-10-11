import Universality.Percolation.VertexMassNonnegativeLimit
import Universality.Percolation.ConditionalMassCharacteristic
import Universality.Probability.L2Characteristic

namespace Universality.Rule.ConfigurationHistory
noncomputable section
open FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem integral_law_complex (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory n → ℂ) :
    ∫ history, observable history ∂law rule p hp hp' hfixed opened n =
      ∑ history, (recursiveWeight rule p opened n history : ℂ) * observable history := by
  rw [law, PMF.integral_eq_sum]
  simp only [finiteWeightPMF_apply, ENNReal.toReal_ofReal
    (recursiveWeight_nonneg rule p hp hp' hfixed opened n _), Complex.real_smul]

theorem integral_infiniteLaw_complex (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory n → ℂ) :
    ∫ path, observable (path n) ∂infiniteLaw rule p hp hp' hfixed opened =
      ∑ fine, ((rule.generation n).network.conditionalCellWeight p opened fine : ℂ) *
        observable (ofFine rule n fine) := by
  rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply n)
    (measurable_of_countable observable).stronglyMeasurable,
    infiniteLaw_marginal, integral_law_complex]
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      joint_observable_law rule p hp hp' hfixed opened n (fun history => (observable history).re)
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using
      joint_observable_law rule p hp hp' hfixed opened n (fun history => (observable history).im)

/-- The common-space characteristic function is the actual conditional graph law. -/
theorem vertexMass_randomCharacteristic (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (state : LiveState) (n : ℕ) (scale t : ℝ) :
    randomCharacteristic (infiniteLaw rule p hp hp' hfixed (state == .connected))
      (fun path => vertexMass rule state n path / scale) t =
      (rule.generation n).network.conditionalInternalCharacteristic p (state == .connected)
        true (state == .both) (t / scale) := by
  unfold randomCharacteristic vertexMass
  rw [integral_infiniteLaw_complex rule p hp hp' hfixed (state == .connected) n
    (fun history => Complex.exp ((t *
      ((rule.generation n).network.internalSelectedMass true (state == .both) (latest rule n history) / scale) : ℝ) * Complex.I))]
  simp only [latest_ofFine, conditionalInternalCharacteristic]
  apply Finset.sum_congr rfl
  intro fine _
  have heq : t * ((rule.generation n).network.internalSelectedMass true (state == .both) fine / scale : ℝ) =
      t / scale * (rule.generation n).network.internalSelectedMass true (state == .both) fine := by ring
  rw [heq]

end
end Universality.Rule.ConfigurationHistory

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- Actual conditional mass characteristic functions converge uniformly on every
bounded frequency interval to the characteristic function of a nonnegative L² law.
This does not assert a density, nonconstancy, or a local limit theorem. -/
theorem Classical.internal_vertex_mass_characteristic_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected), 0 ≤ limit path) ∧
      0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      ∀ bound : ℝ,
        TendstoUniformlyOn
          (fun n t => (rule.generation n).network.conditionalInternalCharacteristic p
            (state == .connected) true (state == .both)
              (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
          (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit))
          atTop {t : ℝ | |t| ≤ bound} := by
  obtain ⟨limit, hlimit, hnonnegative, hmean, hconv⟩ :=
    h.nonnegative_internal_vertex_mass_L2_limit p hp hp' hfixed state
  refine ⟨limit, hlimit, hnonnegative, hmean, fun bound => ?_⟩
  have huniform := L2_characteristic_uniform
    (μ := ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))
    (fun n path => ConfigurationHistory.vertexMass rule state n path /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
    limit
    (fun n => memLp_div_const_real (ConfigurationHistory.memLp_vertexMass rule p hp hp' hfixed state n 2) _)
    hlimit hconv bound
  have heq (n : ℕ) :
      randomCharacteristic (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))
        (fun path => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) =
      fun t => (rule.generation n).network.conditionalInternalCharacteristic p
        (state == .connected) true (state == .both)
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) := by
    funext t
    exact ConfigurationHistory.vertexMass_randomCharacteristic rule p hp hp' hfixed state n _ t
  have hlimitEq :
      randomCharacteristic (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) limit =
      charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit) := by
    funext t
    exact randomCharacteristic_eq_charFun_map hlimit.aestronglyMeasurable t
  simpa only [heq, hlimitEq] using huniform

end
end Universality.Rule


import IGSIII.Mass.VertexMassLimit
import IGSIII.Mass.ConnectedPositivity
import Universality.Percolation.VertexMassCharacteristicLimit

set_option autoImplicit false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- Any L² limit of the actual normalized internal vertex mass has the
characteristic-function convergence required by the exact distributional
smoothing theorem. -/
theorem vertex_mass_L2_limit_characteristic {rule : Rule}
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (state : LiveState)
    (limit : (Π n, rule.ConfigurationHistory n) → ℝ)
    (square_integrable : MemLp limit 2
      (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)))
    (convergence_L2 : Tendsto (fun n => eLpNorm
      ((fun path => ConfigurationHistory.vertexMass rule state n path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
      2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)))
      atTop (𝓝 0)) (bound : ℝ) :
    TendstoUniformlyOn
      (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
      (charFun ((ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point
        (state == .connected)).map limit)) atTop {t : ℝ | |t| ≤ bound} := by
  have uniform := L2_characteristic_uniform
    (μ := ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected))
    (fun n path => ConfigurationHistory.vertexMass rule state n path /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
    limit (fun n => memLp_div_const_real
      (ConfigurationHistory.memLp_vertexMass rule p positive below_one fixed_point state n 2) _)
    square_integrable convergence_L2 bound
  have identity (n : ℕ) :
      randomCharacteristic (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point
        (state == .connected))
        (fun path => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) =
      fun t => (rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) := by
    funext t
    exact ConfigurationHistory.vertexMass_randomCharacteristic rule p positive below_one fixed_point state n _ t
  have limit_identity : randomCharacteristic
      (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected)) limit =
      charFun ((ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point
        (state == .connected)).map limit) := by
    funext t
    exact randomCharacteristic_eq_charFun_map square_integrable.aestronglyMeasurable t
  simpa only [identity, limit_identity] using uniform

/-- The connected internal vertex mass of the actual configuration process
has one common almost-sure and L² limit, and this limit is strictly positive
almost surely. No smoothing identity, positivity claim, or limiting random
variable is assumed as an input. -/
theorem Classical.internal_connected_vertex_mass_ae_L2_positive
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        Tendsto (fun n => ConfigurationHistory.vertexMass rule .connected n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (limit path))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        0 < limit path) ∧
      Tendsto (fun n => eLpNorm
        ((fun path => ConfigurationHistory.vertexMass rule .connected n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
        2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true)) atTop (𝓝 0) := by
  classical
  choose limit square_integrable convergence_ae positive_mean convergence_L2 using
    fun state => classicalRule.internal_vertex_mass_ae_L2_limit p positive below_one fixed_point state
  have nonnegative (state : LiveState) :
      ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
        0 ≤ limit state path := by
    exact nonnegative_L2_limit
      (fun n path => ConfigurationHistory.vertexMass rule state n path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) (limit state)
      (fun n => (memLp_div_const_real
        (ConfigurationHistory.memLp_vertexMass rule p positive below_one fixed_point state n 2) _).aestronglyMeasurable)
      (square_integrable state).aestronglyMeasurable
      (fun n path => div_nonneg (Nat.cast_nonneg _) (pow_nonneg ENNReal.toReal_nonneg n))
      (convergence_L2 state)
  have strict_positive := classicalRule.internal_connected_mass_positive p positive below_one fixed_point
    limit square_integrable nonnegative (positive_mean .connected)
    (fun state bound => vertex_mass_L2_limit_characteristic p positive below_one fixed_point state
      (limit state) (square_integrable state) (convergence_L2 state) bound)
  exact ⟨limit .connected, square_integrable .connected, convergence_ae .connected,
    strict_positive, convergence_L2 .connected⟩

end Universality.Rule

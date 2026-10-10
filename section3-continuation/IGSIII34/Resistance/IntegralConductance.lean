import IGSIII34.Resistance.IntegralJensen
import IGSIII34.Resistance.Jensen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open MeasureTheory

attribute [local irreducible] effectiveResistance conductanceFunctional

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem conductanceFunctional_nonnegative (network : FiniteNetwork Vertex Edge)
    {conductance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ conductance edge) :
    0 ≤ network.conductanceFunctional conductance := by
  unfold conductanceFunctional
  apply le_csInf (network.conductanceEnergies_nonempty conductance)
  rintro value ⟨potential, _, _, rfl⟩
  exact Finset.sum_nonneg (fun edge _ => mul_nonneg (nonnegative edge) (sq_nonneg _))

theorem conductanceFunctional_measurable {Outcome : Type*} [MeasurableSpace Outcome]
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (conductance : Outcome → Edge → ℝ) (measurableInput : Measurable conductance)
    (positive : ∀ outcome edge, 0 < conductance outcome edge) :
    Measurable (fun outcome => network.conductanceFunctional (conductance outcome)) := by
  have inverseMeasurable : Measurable (fun outcome edge => (conductance outcome edge)⁻¹) :=
    measurable_pi_lambda _ (fun edge => ((measurable_pi_apply edge).comp measurableInput).inv)
  have reciprocalMeasurable : Measurable (fun outcome =>
      (network.effectiveResistance (fun edge => (conductance outcome edge)⁻¹))⁻¹) :=
    measurable_inv.comp (network.effectiveResistance_measurable connected
      (fun outcome edge => (conductance outcome edge)⁻¹) inverseMeasurable
      (fun outcome edge => inv_pos.mpr (positive outcome edge)))
  simpa only [network.conductanceFunctional_eq_reciprocalResistance connected (positive _), one_div, Pi.inv_apply]
    using reciprocalMeasurable

theorem conductanceFunctional_le_sum_conductances (network : FiniteNetwork Vertex Edge)
    {conductance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ conductance edge) :
    network.conductanceFunctional conductance ≤ ∑ edge, conductance edge := by
  let potential : Vertex → ℝ := fun vertex => if vertex = network.source then 1 else 0
  have sourceValue : potential network.source = 1 := by simp [potential]
  have targetValue : potential network.target = 0 := by simp [potential, network.distinct.symm]
  apply (network.conductanceFunctional_le_energy nonnegative sourceValue targetValue).trans
  apply Finset.sum_le_sum
  intro edge _
  have squareBound : (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 ≤ 1 := by
    dsimp [potential]
    split_ifs <;> norm_num
  simpa only [mul_one] using mul_le_mul_of_nonneg_left squareBound (nonnegative edge)

theorem conductanceFunctional_integrable {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (conductance : Outcome → Edge → ℝ) (measurableInput : Measurable conductance)
    (positive : ∀ outcome edge, 0 < conductance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => conductance outcome edge) measure) :
    Integrable (fun outcome => network.conductanceFunctional (conductance outcome)) measure := by
  apply (integrable_finsetSum Finset.univ (fun edge _ => inputIntegrable edge)).mono'
    (network.conductanceFunctional_measurable connected conductance measurableInput positive).aestronglyMeasurable
  filter_upwards [] with outcome
  rw [Real.norm_eq_abs, abs_of_nonneg
    (network.conductanceFunctional_nonnegative (fun edge => (positive outcome edge).le))]
  exact network.conductanceFunctional_le_sum_conductances (fun edge => (positive outcome edge).le)

theorem conductanceFunctional_integral_jensen {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (conductance : Outcome → Edge → ℝ) (measurableInput : Measurable conductance)
    (positive : ∀ outcome edge, 0 < conductance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => conductance outcome edge) measure) :
    (∫ outcome, network.conductanceFunctional (conductance outcome) ∂measure) ≤
      network.conductanceFunctional (fun edge => ∫ outcome, conductance outcome edge ∂measure) := by
  unfold conductanceFunctional
  apply le_csInf (network.conductanceEnergies_nonempty _)
  rintro value ⟨potential, sourceValue, targetValue, rfl⟩
  have energyIntegrable := integrable_finsetSum Finset.univ
    (fun edge _ => (inputIntegrable edge).mul_const
      ((potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2))
  have comparison := integral_mono
    (network.conductanceFunctional_integrable measure connected conductance measurableInput positive inputIntegrable)
    energyIntegrable (fun outcome =>
      network.conductanceFunctional_le_energy (fun edge => (positive outcome edge).le) sourceValue targetValue)
  change (∫ outcome, network.conductanceFunctional (conductance outcome) ∂measure) ≤
    ∫ outcome, ∑ edge, conductance outcome edge *
      (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 ∂measure at comparison
  rw [integral_finsetSum Finset.univ
    (fun edge _ => (inputIntegrable edge).mul_const
      ((potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2))] at comparison
  unfold conductanceFunctional at comparison
  simpa only [integral_mul_const, conductanceEnergy] using comparison

theorem reciprocalResistance_integrable {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge)
    (inverseIntegrable : ∀ edge, Integrable (fun outcome => (resistance outcome edge)⁻¹) measure) :
    Integrable (fun outcome => (network.effectiveResistance (resistance outcome))⁻¹) measure := by
  have inverseMeasurable : Measurable (fun outcome edge => (resistance outcome edge)⁻¹) :=
    measurable_pi_lambda _ (fun edge => ((measurable_pi_apply edge).comp measurableInput).inv)
  have outputIdentity : (fun outcome => network.conductanceFunctional
      (fun edge => (resistance outcome edge)⁻¹)) =
      (fun outcome => (network.effectiveResistance (resistance outcome))⁻¹) := by
    funext outcome
    rw [network.conductanceFunctional_eq_reciprocalResistance connected
      (fun edge => inv_pos.mpr (positive outcome edge))]
    simp only [inv_inv, one_div]
  rw [← outputIdentity]
  exact network.conductanceFunctional_integrable measure connected _ inverseMeasurable
    (fun outcome edge => inv_pos.mpr (positive outcome edge)) inverseIntegrable

theorem reciprocalResistance_integral_upper_bound {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge)
    (inverseIntegrable : ∀ edge, Integrable (fun outcome => (resistance outcome edge)⁻¹) measure)
    {inverseMean : ℝ} (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, (∫ outcome, (resistance outcome edge)⁻¹ ∂measure) = inverseMean) :
    (∫ outcome, (network.effectiveResistance (resistance outcome))⁻¹ ∂measure) ≤
      inverseMean / network.effectiveResistance (fun _ => 1) := by
  have inverseMeasurable : Measurable (fun outcome edge => (resistance outcome edge)⁻¹) :=
    measurable_pi_lambda _ (fun edge => ((measurable_pi_apply edge).comp measurableInput).inv)
  have bound := network.conductanceFunctional_integral_jensen measure connected
    (fun outcome edge => (resistance outcome edge)⁻¹) inverseMeasurable
    (fun outcome edge => inv_pos.mpr (positive outcome edge)) inverseIntegrable
  have outputIdentity : (fun outcome => network.conductanceFunctional
      (fun edge => (resistance outcome edge)⁻¹)) =
      (fun outcome => (network.effectiveResistance (resistance outcome))⁻¹) := by
    funext outcome
    rw [network.conductanceFunctional_eq_reciprocalResistance connected
      (fun edge => inv_pos.mpr (positive outcome edge))]
    simp only [inv_inv, one_div]
  have inputIdentity : (fun edge => ∫ outcome, (resistance outcome edge)⁻¹ ∂measure) =
      (fun _ : Edge => inverseMean) := funext commonInverseMean
  rw [outputIdentity, inputIdentity, network.conductanceFunctional_constant connected inverseMeanPositive] at bound
  exact bound

theorem random_resistance_integral_mean_sandwich {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) [IsProbabilityMeasure measure] (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => resistance outcome edge) measure)
    (inverseIntegrable : ∀ edge, Integrable (fun outcome => (resistance outcome edge)⁻¹) measure)
    (commonMean : ∀ edge, (∫ outcome, resistance outcome edge ∂measure) = 1)
    {inverseMean : ℝ} (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, (∫ outcome, (resistance outcome edge)⁻¹ ∂measure) = inverseMean) :
    network.effectiveResistance (fun _ => 1) / inverseMean ≤
      (∫ outcome, network.effectiveResistance (resistance outcome) ∂measure) ∧
    (∫ outcome, network.effectiveResistance (resistance outcome) ∂measure) ≤
      network.effectiveResistance (fun _ => 1) := by
  have outputIntegrable := network.effectiveResistance_integrable measure connected resistance
    measurableInput positive inputIntegrable
  have outputInverseIntegrable := network.reciprocalResistance_integrable measure connected resistance
    measurableInput positive inverseIntegrable
  have reciprocalBound := network.reciprocalResistance_integral_upper_bound measure connected resistance
    measurableInput positive inverseIntegrable inverseMeanPositive commonInverseMean
  have unitResistancePositive := network.effectiveResistance_pos_of_connected connected (fun _ => zero_lt_one)
  let trialScalar := network.effectiveResistance (fun _ => 1) / inverseMean
  have pointwise (outcome : Outcome) :
      2 * trialScalar ≤ network.effectiveResistance (resistance outcome) +
        trialScalar ^ 2 * (network.effectiveResistance (resistance outcome))⁻¹ := by
    have outputPositive := network.effectiveResistance_pos_of_connected connected (positive outcome)
    apply (mul_le_mul_iff_of_pos_right outputPositive).mp
    have cancellation : trialScalar ^ 2 * (network.effectiveResistance (resistance outcome))⁻¹ *
        network.effectiveResistance (resistance outcome) = trialScalar ^ 2 := by
      rw [mul_assoc, inv_mul_cancel₀ outputPositive.ne', mul_one]
    rw [add_mul, cancellation]
    nlinarith [sq_nonneg (network.effectiveResistance (resistance outcome) - trialScalar)]
  have comparison := integral_mono (integrable_const (2 * trialScalar))
    (outputIntegrable.add (outputInverseIntegrable.const_mul (trialScalar ^ 2))) pointwise
  have constantIntegral : (∫ _outcome : Outcome, 2 * trialScalar ∂measure) = 2 * trialScalar := by simp
  rw [constantIntegral] at comparison
  simp only [Pi.add_apply] at comparison
  rw [integral_add outputIntegrable (outputInverseIntegrable.const_mul _), integral_const_mul] at comparison
  have productBound := mul_le_mul_of_nonneg_left reciprocalBound (sq_nonneg trialScalar)
  have scalarIdentity : trialScalar ^ 2 * (inverseMean / network.effectiveResistance (fun _ => 1)) =
      trialScalar := by
    dsimp [trialScalar]
    field_simp [unitResistancePositive.ne', inverseMeanPositive.ne']
  rw [scalarIdentity] at productBound
  constructor
  · change trialScalar ≤ _
    linarith
  · have inputIdentity : (fun edge => ∫ outcome, resistance outcome edge ∂measure) =
        (fun _ : Edge => 1) := funext commonMean
    simpa only [inputIdentity] using network.effectiveResistance_integral_jensen measure connected
      resistance measurableInput positive inputIntegrable

end
end IGSIII34.Resistance.FiniteNetwork

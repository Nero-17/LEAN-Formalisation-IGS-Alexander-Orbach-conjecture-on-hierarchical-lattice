import Universality.Percolation.GenerationMassCharacteristic
import Universality.Percolation.VertexMassCharacteristicLimit

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- Passing the exact finite graph recursion to the L² limits gives their
characteristic-function smoothing equation, without assuming an infinite branching law. -/
theorem Classical.internal_vertex_mass_smoothing {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ,
      (∀ state, MemLp (limit state) 2
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) ∧
      (∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected),
        0 ≤ limit state path) ∧
      (∀ state, 0 < (∫ path, limit state path
        ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) ∧
      (∀ state bound, TendstoUniformlyOn
        (fun n t => (rule.generation n).network.conditionalInternalCharacteristic p
          (state == .connected) true (state == .both)
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
        (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
        atTop {t : ℝ | |t| ≤ bound}) ∧
      (∀ state t, charFun
          ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)) t =
        ∑ coarse, (rule.network.conditionalCellWeight p (state == .connected) coarse : ℂ) *
          ∏ e, match rule.network.childState state coarse e with
            | none => 1
            | some child => charFun
              ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
              (t / (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) := by
  classical
  choose limit hmem hnonnegative hmean huniform using
    fun state => h.internal_vertex_mass_characteristic_limit p hp hp' hfixed state
  refine ⟨limit, hmem, hnonnegative, hmean, huniform, ?_⟩
  intro state t
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hpoint (child : LiveState) (frequency : ℝ) :
      Tendsto (fun n => (rule.generation n).network.conditionalVertexCharacteristic p child
        (frequency / radius ^ n)) atTop
        (𝓝 (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child)) frequency)) :=
    (huniform child |frequency|).tendsto_at (x := frequency)
      (show |frequency| ≤ |frequency| from le_rfl)
  have hleft := (hpoint state t).comp (tendsto_add_atTop_nat 1)
  have hfrequency : Tendsto (fun n : ℕ => t / radius ^ (n + 1)) atTop (𝓝 0) := by
    have hz := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hradius)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hz.const_mul t
  have hright : Tendsto
      (fun n => ∑ coarse, (rule.network.conditionalCellWeight p (state == .connected) coarse : ℂ) *
        Complex.exp (((t / radius ^ (n + 1)) *
          rule.network.internalSelectedMass true (state == .both) coarse : ℝ) * Complex.I) *
          ∏ e, match rule.network.childState state coarse e with
            | none => 1
            | some child => (rule.generation n).network.conditionalVertexCharacteristic p child
                (t / radius ^ (n + 1))) atTop
      (𝓝 (∑ coarse, (rule.network.conditionalCellWeight p (state == .connected) coarse : ℂ) *
        ∏ e, match rule.network.childState state coarse e with
          | none => 1
          | some child => charFun
              ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
              (t / radius))) := by
    apply tendsto_finset_sum
    intro coarse _
    have hreward : Tendsto
        (fun n => Complex.exp (((t / radius ^ (n + 1)) *
          rule.network.internalSelectedMass true (state == .both) coarse : ℝ) * Complex.I))
        atTop (𝓝 1) := by
      simpa only [Function.comp_def, zero_mul, Complex.ofReal_zero, Complex.exp_zero] using
        Complex.continuous_exp.continuousAt.tendsto.comp
          ((Complex.continuous_ofReal.continuousAt.tendsto.comp
            (hfrequency.mul_const (rule.network.internalSelectedMass true (state == .both) coarse : ℝ))).mul_const Complex.I)
    have hproduct : Tendsto
        (fun n => ∏ e, match rule.network.childState state coarse e with
          | none => (1 : ℂ)
          | some child => (rule.generation n).network.conditionalVertexCharacteristic p child
            (t / radius ^ (n + 1))) atTop
        (𝓝 (∏ e, match rule.network.childState state coarse e with
          | none => (1 : ℂ)
          | some child => charFun
              ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
              (t / radius))) := by
      apply tendsto_finset_prod
      intro edge _
      cases hchild : rule.network.childState state coarse edge with
      | none => exact tendsto_const_nhds
      | some child =>
        have heq (n : ℕ) : t / radius ^ (n + 1) = (t / radius) / radius ^ n := by
          rw [pow_succ]
          ring
        simpa only [heq] using hpoint child (t / radius)
    simpa only [mul_one] using (hreward.const_mul
      (rule.network.conditionalCellWeight p (state == .connected) coarse : ℂ)).mul hproduct
  have hexact (n : ℕ) := rule.generation_conditionalVertexCharacteristic h.massAdmissible.symmetric
    p hp hp' hfixed n state (t / radius ^ (n + 1))
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun n => (hexact n).symm)))

end
end Universality.Rule

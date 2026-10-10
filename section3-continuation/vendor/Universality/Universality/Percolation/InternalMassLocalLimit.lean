import Universality.Percolation.MassCharacteristicL1
import Universality.Probability.LatticeLocalLimit
import Universality.Percolation.ConditionalMassInversion

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual conditional internal mass obeys a uniform lattice local limit
with the inverse characteristic transform of its genuine branching limit. -/
theorem Classical.internal_mass_local_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ,
      (∀ state, MemLp (limit state) 2
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) ∧
      (∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected),
        0 ≤ limit state path) ∧
      (∀ state, 0 < ∫ path, limit state path
        ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      (∀ state bound, TendstoUniformlyOn
        (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
        (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
        atTop {t : ℝ | |t| ≤ bound}) ∧
      ∀ state,
        Integrable (charFun
          ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state))) ∧
        ∀ error > 0, ∀ᶠ n : ℕ in atTop, ∀ size : ℕ,
          ‖(((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n : ℂ) *
              ((rule.generation n).network.conditionalInternalMassProbability p (state == .connected)
                true (state == .both) size : ℂ) -
            inverseCharacteristic
              (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
              ((size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)‖ < error := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  obtain ⟨limit, hmem, hnonnegative, hmean, huniform, hL1⟩ := h.internal_mass_truncated_characteristic_L1 p hp hp' hfixed
  refine ⟨limit, hmem, hnonnegative, hmean, huniform, ?_⟩
  intro state
  refine ⟨(hL1 state).1, ?_⟩
  have hllt := lattice_local_limit_of_L1
    (fun n => Configuration (rule.generation n).edges)
    (fun n configuration => ((rule.generation n).network.conditionalCellWeight p (state == .connected) configuration : ℂ))
    (fun n => (rule.generation n).network.internalSelectedMass true (state == .both))
    (fun n => radius ^ n) (fun n => pow_pos (zero_lt_one.trans hradius) n)
    (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
    (hL1 state).1 (by
      simpa only [truncatedLatticeCharacteristic, conditionalVertexCharacteristic,
        conditionalInternalCharacteristic, Complex.ofReal_mul, Complex.ofReal_natCast] using (hL1 state).2)
  simpa only [conditionalInternalMassProbability, Complex.ofReal_sum, Complex.ofReal_zero,
    Complex.ofReal_pow, apply_ite] using hllt

end
end Universality.Rule

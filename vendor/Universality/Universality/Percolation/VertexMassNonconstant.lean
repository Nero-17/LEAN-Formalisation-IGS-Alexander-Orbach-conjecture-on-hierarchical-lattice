import Universality.Percolation.VertexMassSmoothing
import Universality.Percolation.AllClosedCharacteristic
import Universality.Percolation.MassSpectralLowerBound

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- The positive mean and the all-closed branch rule out a deterministic
single-terminal limit, because its offspring degree is strictly below the Perron scale. -/
theorem Classical.single_mass_smoothing_nonconstant {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
    (hmem : ∀ state, MemLp (limit state) 2
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (hmean : 0 < (∫ path, limit .single path
      ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false))
    (hsmoothing : ∀ t, charFun
        ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single)) t =
      ∑ coarse, (rule.network.conditionalCellWeight p false coarse : ℂ) *
        ∏ e, match rule.network.childState .single coarse e with
          | none => 1
          | some child => charFun
            ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
            (t / (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) :
    ¬ ∃ constant : ℝ, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false,
      limit .single path = constant := by
  rintro ⟨constant, hconstant⟩
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  let degree := rule.network.sourceIncidentEdges.card
  have hpositive : 0 < constant := by
    rw [integral_congr_ae hconstant] at hmean
    simpa using hmean
  have hgap : (degree : ℝ) < radius := by
    simpa only [degree, rule.network.sourceIncidentEdges_card_eq_degree h.simple] using
      h.terminal_degree_lt_mass_spectralRadius p hp hp'
  have hradius : 0 < radius := (Nat.cast_nonneg degree).trans_lt hgap
  have hsingleMem : MemLp (limit .single) 2
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false) := hmem .single
  have hphase (t : ℝ) : charFun
      ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single)) t =
        Complex.exp ((t * constant : ℝ) * Complex.I) := by
    rw [← randomCharacteristic_eq_charFun_map hsingleMem.aestronglyMeasurable]
    unfold randomCharacteristic
    rw [integral_congr_ae (hconstant.mono (fun _ hx => by rw [hx]))]
    simp
  have hvalues (t : ℝ) (child : LiveState) :
      ‖charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map
        (limit child)) (t / radius)‖ ≤ 1 := by
    letI := Measure.isProbabilityMeasure_map (hmem child).aestronglyMeasurable.aemeasurable
    exact norm_charFun_le_one _
  have hequal : (degree : ℝ) * constant / radius = constant := by
    apply real_eq_of_characteristic_phases
    intro t
    have hbranch := rule.network.allClosed_characteristic_unit_branch p hp hp' hfixed
      (fun child => charFun
        ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
        (t / radius)) (Complex.exp ((t * constant : ℝ) * Complex.I))
      (hvalues t) (Complex.norm_exp_ofReal_mul_I _) (by rw [← hphase]; exact hsmoothing t)
    change (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single))
      (t / radius)) ^ degree = _ at hbranch
    rw [hphase, ← Complex.exp_nat_mul] at hbranch
    convert hbranch using 1 <;> congr 1 <;> push_cast <;> ring
  have hproduct : (degree : ℝ) * constant = constant * radius :=
    (div_eq_iff hradius.ne').mp hequal
  nlinarith

/-- The actual normalized single-terminal internal-mass laws converge to a
nonnegative, positive-mean, nonconstant law. -/
theorem Classical.internal_single_mass_nonconstant_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false, 0 ≤ limit path) ∧
      0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false) ∧
      (¬ ∃ constant : ℝ, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false,
        limit path = constant) ∧
      ∀ bound : ℝ, TendstoUniformlyOn
        (fun n t => (rule.generation n).network.conditionalInternalCharacteristic p false true false
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
        (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map limit))
        atTop {t : ℝ | |t| ≤ bound} := by
  obtain ⟨limit, hmem, hnonnegative, hmean, huniform, hsmoothing⟩ :=
    h.internal_vertex_mass_smoothing p hp hp' hfixed
  exact ⟨limit .single, hmem .single, hnonnegative .single, hmean .single,
    h.single_mass_smoothing_nonconstant p hp hp' hfixed limit hmem (hmean .single)
      (hsmoothing .single), huniform .single⟩

end
end Universality.Rule

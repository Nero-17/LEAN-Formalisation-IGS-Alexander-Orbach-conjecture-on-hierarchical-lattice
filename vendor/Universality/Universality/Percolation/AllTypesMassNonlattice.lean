import Universality.Percolation.VertexMassNonlattice
import Universality.Percolation.CharacteristicPropagation

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

theorem Classical.mass_smoothing_nonlattice {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
    (hmem : ∀ state, MemLp (limit state) 2
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (hmean : 0 < (∫ path, limit .single path
      ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false))
    (hsmoothing : ∀ state t, charFun
        ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)) t =
      ∑ coarse, (rule.network.conditionalCellWeight p (state == .connected) coarse : ℂ) *
        ∏ e, match rule.network.childState state coarse e with
          | none => 1
          | some child => charFun
            ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
            (t / (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))
    (state : LiveState) (t : ℝ) (ht : t ≠ 0) :
    ‖charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)) t‖ < 1 := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  let characteristic (state : LiveState) := charFun
    ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state))
  have hradius : 0 < radius := (zero_lt_one.trans
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale)).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hnorm (child : LiveState) (frequency : ℝ) : ‖characteristic child frequency‖ ≤ 1 := by
    letI := Measure.isProbabilityMeasure_map (hmem child).aestronglyMeasurable.aemeasurable
    exact norm_charFun_le_one _
  have hsingle (frequency : ℝ) (hne : frequency ≠ 0) : ‖characteristic .single frequency‖ < 1 :=
    h.single_mass_smoothing_nonlattice p hp hp' hfixed limit hmem hmean (hsmoothing .single) frequency hne
  have hboth (frequency : ℝ) (hne : frequency ≠ 0) : ‖characteristic .both frequency‖ < 1 := by
    by_contra hnot
    have hunit : ‖characteristic .both frequency‖ = 1 := le_antisymm (hnorm _ _) (le_of_not_gt hnot)
    obtain ⟨edge, hincident⟩ := rule.network.exists_source_incident_edge (h.connected _)
    obtain ⟨hfirst, hsecond⟩ := rule.network.incident_endpoints_ne_target edge hincident h.scale
    have hchild := rule.network.childState_allClosed_both_single edge hincident hfirst hsecond
    have hclosed := rule.network.child_characteristic_unit_of_smoothing p hp hp' hfixed .both
      (fun child => characteristic child (frequency / radius)) (characteristic .both frequency)
      (fun child => hnorm child _) hunit (hsmoothing .both frequency)
      (fun _ => false) edge .single
      (rule.network.conditionalCellWeight_allClosed_pos p hp hp' hfixed) hchild
    exact (hsingle (frequency / radius) (div_ne_zero hne hradius.ne')).ne hclosed
  cases state with
  | single => exact hsingle t ht
  | both => exact hboth t ht
  | connected =>
    by_contra hnot
    have hunit : ‖characteristic .connected t‖ = 1 := le_antisymm (hnorm _ _) (le_of_not_gt hnot)
    obtain ⟨edge, hchild⟩ := rule.network.exists_closed_edge_both_endpoints_active (h.connected _) h.cut
    have hpositive : 0 < rule.network.conditionalCellWeight p true (onlyClosed edge) := by
      simp only [conditionalCellWeight, h.cut edge, if_pos rfl,
        ↓reduceIte, hfixed]
      exact div_pos (bernoulliWeight_pos hp hp' _) hp
    have hclosed := rule.network.child_characteristic_unit_of_smoothing p hp hp' hfixed .connected
      (fun child => characteristic child (t / radius)) (characteristic .connected t)
      (fun child => hnorm child _) hunit (hsmoothing .connected t)
      (onlyClosed edge) edge .both hpositive hchild
    exact (hboth (t / radius) (div_ne_zero ht hradius.ne')).ne hclosed

/-- All three actual conditional mass laws have a nonlattice limit, with
uniform convergence of their characteristic functions on bounded intervals. -/
theorem Classical.internal_vertex_mass_nonlattice_limits {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ,
      (∀ state, MemLp (limit state) 2
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) ∧
      (∀ state t, t ≠ 0 → ‖charFun
        ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)) t‖ < 1) ∧
      ∀ state bound, TendstoUniformlyOn
        (fun n t => (rule.generation n).network.conditionalInternalCharacteristic p
          (state == .connected) true (state == .both)
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
        (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
        atTop {t : ℝ | |t| ≤ bound} := by
  obtain ⟨limit, hmem, _, hmean, huniform, hsmoothing⟩ := h.internal_vertex_mass_smoothing p hp hp' hfixed
  exact ⟨limit, hmem, h.mass_smoothing_nonlattice p hp hp' hfixed limit hmem (hmean .single) hsmoothing,
    huniform⟩

end
end Universality.Rule

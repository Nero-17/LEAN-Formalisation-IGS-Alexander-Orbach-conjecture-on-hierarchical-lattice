import Universality.Percolation.MassSupportTransfer
import Universality.Probability.ScaledSumFullSupport
import Universality.Percolation.MassSpectralUpperBound
import Universality.Percolation.MassSpectralLowerBound

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- Full positive support follows from three concrete offspring branches:
all-closed single, all-open connected, and one source-incident open edge. -/
theorem Classical.mass_smoothing_full_positive_support {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (hnonnegative : ∀ state, (law state).support ⊆ Set.Ici 0)
    (hmean : 0 < ∫ x, x ∂law .connected)
    (hsmoothing : ∀ state, law state = finiteMixtureLaw (rule.network.conditionalCellWeight p (state == .connected))
      (rule.network.offspringMassLaw law
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) state))
    (x : ℝ) (hx : 0 < x) : x ∈ (law .single).support := by
  classical
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  have hdegree : 2 ≤ rule.network.sourceIncidentEdges.card :=
    rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
  have hdegreeRadius : (rule.network.sourceIncidentEdges.card : ℝ) < radius := by
    rw [rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    exact h.terminal_degree_lt_mass_spectralRadius p hp hp'
  have hsum (value : Fin rule.network.sourceIncidentEdges.card → ℝ)
      (hvalue : ∀ i, value i ∈ (law .single).support) :
      (∑ i, value i) / radius ∈ (law .single).support :=
    rule.network.allClosed_single_support_sum law p radius hp hp' hfixed (hsmoothing .single) value hvalue
  have hzero : 0 ∈ (law .single).support :=
    scaled_sum_support_zero _ _ radius Measure.isClosed_support
      ((law .single).nonempty_support (IsProbabilityMeasure.ne_zero _)) hradius0 hdegreeRadius hsum
  obtain ⟨point, hpointPos, hpoint⟩ := exists_positive_support_of_positive_mean (law .connected) hmean
  let ratio := (rule.edges : ℝ) / radius
  have hratio : 1 < ratio := (one_lt_div hradius0).mpr (h.mass_spectralRadius_lt_edges p hp hp')
  have hconnectedPoint (n : ℕ) : point * ratio ^ n ∈ (law .connected).support := by
    induction n with
    | zero => simpa using hpoint
    | succ n ih =>
      have hnext := rule.network.allOpen_connected_support_scale law p radius hp hp'
        h.connected hfixed (hsmoothing .connected) _ ih
      convert hnext using 1 <;> dsimp [ratio] <;> rw [pow_succ] <;> ring
  obtain ⟨edge, hincident⟩ := rule.network.exists_source_incident_edge (h.connected _)
  obtain ⟨hfirst, hsecond⟩ := rule.network.incident_endpoints_ne_target edge hincident h.scale
  have hpositive : 0 < rule.network.conditionalCellWeight p false (onlyOpen edge) := by
    simp only [conditionalCellWeight, rule.network.crosses_onlyOpen_false edge hfirst hsecond,
      if_pos rfl, Bool.false_eq_true, ↓reduceIte, hfixed]
    exact div_pos (bernoulliWeight_pos hp hp' _) (sub_pos.mpr hp')
  obtain ⟨offset, hoffset, htransfer⟩ := rule.network.smoothing_support_affine_transfer law hnonnegative
    p radius hradius0 .single .connected (hsmoothing .single) (onlyOpen edge) hpositive edge
    (rule.network.childState_onlyOpen .single edge hincident)
  let sequence (n : ℕ) := point * ratio ^ n / radius + offset
  have hsequence (n : ℕ) : sequence n ∈ (law .single).support := htransfer _ (hconnectedPoint n)
  have hsequence0 : 0 ≤ sequence 0 := by
    dsimp [sequence]
    positivity
  have hunbounded : Tendsto sequence atTop atTop := by
    have hscaled : Tendsto (fun n : ℕ => (point / radius) * ratio ^ n) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hratio).const_mul_atTop (div_pos hpointPos hradius0)
    apply tendsto_atTop_mono _ hscaled
    intro n
    dsimp [sequence]
    calc
      point / radius * ratio ^ n = point * ratio ^ n / radius := by ring
      _ ≤ point * ratio ^ n / radius + offset := le_add_of_nonneg_right hoffset
  have hstep (n : ℕ) : sequence (n + 1) ≤ ratio * sequence n := by
    have heq : sequence (n + 1) = ratio * sequence n - (ratio - 1) * offset := by
      dsimp [sequence]
      rw [pow_succ]
      ring
    rw [heq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio.le) hoffset]
  exact scaled_sum_full_positive_support _ _ radius ratio Measure.isClosed_support hdegree
    hdegreeRadius (zero_lt_one.trans hratio).le hzero hsum sequence hsequence hsequence0 hunbounded hstep x hx

end
end Universality.Rule

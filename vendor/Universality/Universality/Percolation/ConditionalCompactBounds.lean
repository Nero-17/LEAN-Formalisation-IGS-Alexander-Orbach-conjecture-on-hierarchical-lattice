import Universality.Percolation.BernoulliMonotonicity
import Universality.Percolation.VertexMomentComparison

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem bernoulliWeight_uniform_lower (lower upper p : ℝ) (hlower : 0 < lower) (hupper : upper < 1)
    (hp : lower ≤ p) (hp' : p ≤ upper) (configuration : Configuration edges) :
    (min lower (1 - upper)) ^ edges ≤ bernoulliWeight p configuration := by
  unfold bernoulliWeight
  have hmin : 0 < min lower (1 - upper) := lt_min hlower (sub_pos.mpr hupper)
  have hprod : (∏ _ : Fin edges, min lower (1 - upper)) ≤
      ∏ edge : Fin edges, if configuration edge then p else 1 - p := by
    apply Finset.prod_le_prod
    · intro edge _
      exact hmin.le
    · intro edge _
      split
      · exact (min_le_left _ _).trans hp
      · exact (min_le_right _ _).trans (by linarith)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

theorem conditioningProbability_le_one {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (state : LiveState) :
    R.conditioningProbability p state ≤ 1 := by
  calc
    _ ≤ ∑ configuration : Configuration edges, bernoulliWeight p configuration := by
      apply Finset.sum_le_sum
      intro configuration _
      split
      · exact le_rfl
      · exact bernoulliWeight_nonneg hp hp' _
    _ = 1 := sum_bernoulliWeight p

theorem exists_positive_internal_mass_configuration
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) (state : LiveState) :
    ∃ configuration : Configuration edges, R.conditioning state configuration = true ∧
      0 < R.internalSelectedMass true (state == .both) configuration := by
  obtain ⟨edge, hincident⟩ := R.exists_source_incident_edge hconnected
  obtain ⟨hfirst, hsecond⟩ := R.incident_endpoints_ne_target edge hincident hscale
  cases state
  · refine ⟨fun _ => true, ?_, ?_⟩
    · exact (R.crosses_eq_true _).mpr hconnected
    · exact R.internalSelectedMass_pos_of_open_incident _ _ edge rfl hincident hfirst hsecond
  · refine ⟨onlyOpen edge, ?_, ?_⟩
    · simp only [conditioning, R.crosses_onlyOpen_false edge hfirst hsecond, Bool.not_false]
    · exact R.internalSelectedMass_pos_of_open_incident _ _ edge (by simp [onlyOpen]) hincident hfirst hsecond
  · refine ⟨onlyOpen edge, ?_, ?_⟩
    · simp only [conditioning, R.crosses_onlyOpen_false edge hfirst hsecond, Bool.not_false]
    · exact R.internalSelectedMass_pos_of_open_incident _ _ edge (by simp [onlyOpen]) hincident hfirst hsecond

theorem conditionalVertexMoment_ge_positive_configuration {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (state : LiveState) (configuration : Configuration edges)
    (hcondition : R.conditioning state configuration = true)
    (hmass : 0 < R.internalSelectedMass true (state == .both) configuration) (order : ℕ) :
    bernoulliWeight p configuration ≤ R.conditionalVertexMoment p state order := by
  have hprobability := (R.conditioningProbability_pos_iff hp hp' state).mpr ⟨configuration, hcondition⟩
  have hweight : bernoulliWeight p configuration ≤ R.conditionalCellWeight p (state == .connected) configuration := by
    rw [R.conditionalCellWeight_reference, hcondition, if_pos rfl]
    apply (le_div_iff₀ hprobability).mpr
    exact (mul_le_mul_of_nonneg_left (R.conditioningProbability_le_one hp.le hp'.le state)
      (bernoulliWeight_pos hp hp' _).le).trans_eq (mul_one _)
  have hmassOne : (1 : ℝ) ≤ R.internalSelectedMass true (state == .both) configuration := by exact_mod_cast (by omega : 1 ≤ R.internalSelectedMass true (state == .both) configuration)
  calc
    _ ≤ R.conditionalCellWeight p (state == .connected) configuration := hweight
    _ ≤ R.conditionalCellWeight p (state == .connected) configuration *
        (R.internalSelectedMass true (state == .both) configuration : ℝ) ^ order :=
      le_mul_of_one_le_right (R.conditionalCellWeight_nonneg hp.le hp'.le _ _) (one_le_pow₀ hmassOne)
    _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
      (f := fun cell => R.conditionalCellWeight p (state == .connected) cell *
        (R.internalSelectedMass true (state == .both) cell : ℝ) ^ order)
      (fun cell _ => mul_nonneg (R.conditionalCellWeight_nonneg hp.le hp'.le (state == .connected) cell)
        (pow_nonneg (Nat.cast_nonneg _) _)) (Finset.mem_univ configuration)

/-- A fixed positive configuration in each live state gives the same
explicit positive lower bound for every moment order throughout an interior
compact parameter interval. -/
theorem conditionalVertexMoment_uniform_lower (lower upper p : ℝ)
    (hlower : 0 < lower) (hupper : upper < 1) (hp : lower ≤ p) (hp' : p ≤ upper)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) (state : LiveState) (order : ℕ) :
    (min lower (1 - upper)) ^ edges ≤ R.conditionalVertexMoment p state order := by
  obtain ⟨configuration, hcondition, hmass⟩ := R.exists_positive_internal_mass_configuration hconnected hscale state
  exact (bernoulliWeight_uniform_lower lower upper p hlower hupper hp hp' configuration).trans
    (R.conditionalVertexMoment_ge_positive_configuration (hlower.trans_le hp) (hp'.trans_lt hupper)
      state configuration hcondition hmass order)

theorem conditionalCellWeight_le_reciprocal (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (denominator : ℝ) (hdenominator : 0 < denominator)
    (hcross : denominator ≤ R.reliability p) (hfail : denominator ≤ 1 - R.reliability p)
    (opened : Bool) (configuration : Configuration edges) :
    R.conditionalCellWeight p opened configuration ≤ 1 / denominator := by
  have hweight : bernoulliWeight p configuration ≤ 1 := by
    have hs := Finset.single_le_sum (s := Finset.univ) (f := bernoulliWeight p)
      (fun cell _ => bernoulliWeight_nonneg hp.le hp'.le cell) (Finset.mem_univ configuration)
    simpa only [sum_bernoulliWeight] using hs
  unfold conditionalCellWeight
  have hden : denominator ≤ if opened then R.reliability p else 1 - R.reliability p := by
    cases opened <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption
  apply div_le_div₀ zero_le_one (by split; exact hweight; norm_num) hdenominator hden


theorem conditionalCellWeight_ge_bernoulliWeight (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened : Bool) (configuration : Configuration edges) (hmatch : R.crosses configuration = opened) :
    bernoulliWeight p configuration ≤ R.conditionalCellWeight p opened configuration := by
  unfold conditionalCellWeight
  rw [if_pos hmatch]
  have hdenpos : 0 < if opened then R.reliability p else 1 - R.reliability p := by
    cases opened <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sub_pos.mpr hless
    · exact hpositive
  have hdenle : (if opened then R.reliability p else 1 - R.reliability p) ≤ 1 := by
    cases opened <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · linarith [R.reliability_nonneg hp.le hp'.le]
    · exact R.reliability_le_one hp.le hp'.le
  apply (le_div_iff₀ hdenpos).mpr
  exact (mul_le_mul_of_nonneg_left hdenle (bernoulliWeight_pos hp hp' _).le).trans_eq (mul_one _)

/-- One constant compares all actual conditional configuration weights to
any fixed interior reference parameter uniformly on an interior compact
interval. Fixed zero weights are handled by the crossing event itself. -/
theorem conditionalCellWeight_compact_comparison (critical lower upper : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (hupper : upper < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    ∃ factor : ℝ, 1 ≤ factor ∧ ∀ p, lower ≤ p → p ≤ upper → ∀ opened configuration,
      R.conditionalCellWeight p opened configuration ≤
        factor * R.conditionalCellWeight critical opened configuration := by
  let denominator := min (R.reliability lower) (1 - R.reliability upper)
  have hlower' : lower < 1 := hinterval.trans_lt hupper
  have hupperPos : 0 < upper := hlower.trans_le hinterval
  have hdenominator : 0 < denominator := lt_min
    ((R.reliability_pos_iff_connected hlower hlower').mpr hconnected)
    (sub_pos.mpr (R.reliability_lt_one hupperPos hupper))
  let referenceWeight := (min critical (1 - critical)) ^ edges
  have href : 0 < referenceWeight := pow_pos (lt_min hc (sub_pos.mpr hc')) _
  refine ⟨max 1 (1 / (denominator * referenceWeight)), le_max_left _ _, ?_⟩
  intro p hp hp' opened configuration
  by_cases hmatch : R.crosses configuration = opened
  · have hlowerCross : denominator ≤ R.reliability p :=
      (min_le_left _ _).trans (R.reliability_monotoneOn ⟨hlower.le, hlower'.le⟩
        ⟨(hlower.trans_le hp).le, (hp'.trans_lt hupper).le⟩ hp)
    have hupperCross : denominator ≤ 1 - R.reliability p := by
      have hmono := R.reliability_monotoneOn
        ⟨(hlower.trans_le hp).le, (hp'.trans_lt hupper).le⟩ ⟨hupperPos.le, hupper.le⟩ hp'
      exact (min_le_right _ _).trans (by linarith)
    have hreference : referenceWeight ≤ R.conditionalCellWeight critical opened configuration :=
      (bernoulliWeight_uniform_lower critical critical critical hc hc' le_rfl le_rfl configuration).trans
        (R.conditionalCellWeight_ge_bernoulliWeight critical hc hc'
          ((R.reliability_pos_iff_connected hc hc').mpr hconnected) (R.reliability_lt_one hc hc') opened configuration hmatch)
    calc
      _ ≤ 1 / denominator := R.conditionalCellWeight_le_reciprocal p (hlower.trans_le hp) (hp'.trans_lt hupper)
        denominator hdenominator hlowerCross hupperCross opened configuration
      _ = (1 / (denominator * referenceWeight)) * referenceWeight := by field_simp [hdenominator.ne', href.ne']
      _ ≤ max 1 (1 / (denominator * referenceWeight)) * referenceWeight :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) href.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hreference (zero_le_one.trans (le_max_left _ _))
  · simp only [conditionalCellWeight, hmatch, ↓reduceIte, zero_div, mul_zero, le_refl]

end
end Universality.FiniteNetwork

import Universality.Percolation.PostexitEscapingMassComparison
import Universality.Percolation.ExitFirstMomentLower
import Universality.Percolation.RootMassMonotonicity
import Universality.Percolation.MomentExitWideCompact
import Universality.Percolation.ExitMomentComparison

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0

theorem Classical.escaping_root_mass_exit_bounds {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ neighborhood : ℝ, 0 < neighborhood ∧ neighborhood < critical ∧ neighborhood < 1 - critical ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ neighborhood → ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
        ∀ p, critical < p → p < 1 → |p - critical| < radius →
          lower * (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / (rule.edges : ℝ)) ^ (rule.reliabilityExitTime critical radius p) ≤
            rule.escapingRootMass p ∧
          rule.escapingRootMass p ≤ upper * (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) / (rule.edges : ℝ)) ^
            (rule.reliabilityExitTime critical radius p) := by
  obtain ⟨firstRadius, firstLower, hfirstRadius, hfirstLower, hfirst⟩ :=
    h.exit_first_moment_uniform_lower critical hc hc' hfixed
  obtain ⟨hwideLower, hwideUpper, hwideInterval⟩ := h.reliability_wide_compact critical hc hc'
  obtain ⟨secondRadius, hsecondRadius, hsecond⟩ := h.exit_moment_initial_bound critical
    (rule.network.reliability (critical / 2)) (rule.network.reliability ((1 + critical) / 2))
    hc hc' hfixed hwideLower hwideInterval hwideUpper
  obtain ⟨constant, hconstant, hupper⟩ := hsecond 1
  let neighborhood := min firstRadius (min secondRadius (min (critical / 2) ((1 - critical) / 2)))
  have hneighborhood : 0 < neighborhood := lt_min hfirstRadius
    (lt_min hsecondRadius (lt_min (by linarith) (by linarith)))
  have hnfirst : neighborhood ≤ firstRadius := min_le_left _ _
  have hnsecond : neighborhood ≤ secondRadius := (min_le_right _ _).trans (min_le_left _ _)
  have hncritical : neighborhood ≤ critical / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hnone : neighborhood ≤ (1 - critical) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hvertices : 0 < (rule.vertices : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt h.vertices_gt_two)
  have hedges : 0 < (rule.edges : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt h.edges_gt_one)
  have hgrowth : 1 < ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) :=
    (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1
  refine ⟨neighborhood, hneighborhood, by linarith, by linarith, ?_⟩
  intro radius hradius hradiusSmall
  have hradiusCritical : radius ≤ critical / 2 := hradiusSmall.trans hncritical
  have hradiusOne : radius ≤ (1 - critical) / 2 := hradiusSmall.trans hnone
  have htheta : 0 < rule.escapingRootMass (critical + radius) :=
    h.supercritical_escaping_root_mass_pos critical (critical + radius) hc hc' hfixed (by linarith) (by linarith)
  refine ⟨firstLower / (2 * (rule.vertices : ℝ)) * rule.escapingRootMass (critical + radius), constant,
    mul_pos (div_pos hfirstLower (mul_pos (by norm_num) hvertices)) htheta,
    zero_lt_one.trans_le hconstant, ?_⟩
  intro p hpc hp' hnear
  have hp := hc.trans hpc
  have hne : p ≠ critical := ne_of_gt hpc
  let depth := rule.reliabilityExitTime critical radius p
  let exitParameter := rule.network.reliability^[depth] p
  have hdepth : 0 < depth := h.reliability_exit_pos critical radius p hc hc' hfixed
    (by linarith) (by linarith) hp hp' hne hnear
  obtain ⟨previous, hprevious⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdepth)
  change depth = previous + 1 at hprevious
  have hbefore (j : ℕ) (hj : j ≤ previous) : |rule.network.reliability^[j] p - critical| < radius :=
    h.reliability_exit_before critical radius p hc hc' hfixed (by linarith) (by linarith)
      hp hp' hne j (by dsimp [depth] at hprevious; omega)
  have hwide := h.reliability_exit_wide_compact critical radius p hc hc' hfixed hradius
    hradiusCritical hradiusOne hp hp' hne hnear
  have hexit : 0 < exitParameter := hwideLower.trans_le hwide.1
  have hexit' : exitParameter < 1 := hwide.2.trans_lt hwideUpper
  have hside := ((h.reliability_exit_compact critical radius hc hc' hfixed hradius
    (by linarith) (by linarith)).2.2.2.2 p hp hp' hne hnear).2.2 hpc
  have hthetaLower : rule.escapingRootMass (critical + radius) ≤ rule.escapingRootMass exitParameter :=
    rule.escapingRootMass_monotoneOn h.edges_gt_one h.vertices_gt_two
      ⟨by linarith, by linarith⟩ ⟨hexit.le, hexit'.le⟩ hside
  have hthetaUpper := (rule.escapingRootMass_bounds h.edges_gt_one h.vertices_gt_two hexit.le hexit'.le).2
  have hmassLower (state : LiveState) : firstLower * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth ≤
      (rule.generation depth).network.conditionalVertexMass p state := by
    rw [hprevious]
    exact hfirst p hp hp' previous (fun j hj => (hbefore j hj).trans_le (hradiusSmall.trans hnfirst)) state
  have hbaseLower (state : LiveState) :
      (firstLower / (2 * (rule.vertices : ℝ)) * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth) *
          (rule.network.conditionalVertexMass exitParameter state + rule.vertices) ≤
        (rule.generation depth).network.conditionalVertexMass p state := by
    have hv := rule.network.conditionalVertexMass_le_vertices hexit.le hexit'.le
      ((rule.network.reliability_pos_iff_connected hexit hexit').mpr (h.connected _))
      (rule.network.reliability_lt_one hexit hexit') state
    calc
      _ ≤ (firstLower / (2 * (rule.vertices : ℝ)) * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth) * (2 * (rule.vertices : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
      _ = firstLower * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth := by field_simp [hvertices.ne'] <;> ring
      _ ≤ _ := hmassLower state
  have hbaseUpper : ∀ state k, k ≤ 1 →
      (rule.generation depth).network.conditionalVertexMoment p state k ≤
        (constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth) ^ k * rule.network.conditionalVertexMoment exitParameter state k := by
    intro state k hk
    have hh := hupper p hp hp' previous
      (fun j hj => (hbefore j hj).trans_le (hradiusSmall.trans hnsecond)) exitParameter
      (by rw [← hprevious]) hwide.1 hwide.2 state k hk
    rw [hprevious]
    simpa only [Nat.succ_eq_add_one] using hh
  have hlowerComparison := h.postexit_escaping_mass_lower p exitParameter hp hp' hexit hexit' depth rfl
    (firstLower / (2 * (rule.vertices : ℝ)) * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth) (by positivity) hbaseLower
  have hupperComparison := h.postexit_escaping_mass_upper p exitParameter hp hp' hexit hexit' depth rfl
    (constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth)
    (hconstant.trans (le_mul_of_one_le_right (zero_le_one.trans hconstant) (one_le_pow₀ hgrowth.le))) hbaseUpper
  change _ ≤ rule.escapingRootMass p ∧ rule.escapingRootMass p ≤ _
  constructor
  · calc
      _ = (firstLower / (2 * (rule.vertices : ℝ)) * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth / (rule.edges : ℝ) ^ depth) *
          rule.escapingRootMass (critical + radius) := by rw [div_pow]; ring
      _ ≤ (firstLower / (2 * (rule.vertices : ℝ)) * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth / (rule.edges : ℝ) ^ depth) *
          rule.escapingRootMass exitParameter := mul_le_mul_of_nonneg_left hthetaLower (by positivity)
      _ ≤ _ := hlowerComparison
  · calc
      _ ≤ (constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth / (rule.edges : ℝ) ^ depth) * rule.escapingRootMass exitParameter := hupperComparison
      _ ≤ (constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ depth / (rule.edges : ℝ) ^ depth) * 1 :=
        mul_le_mul_of_nonneg_left hthetaUpper (by positivity)
      _ = _ := by rw [div_pow]; ring

end
end Universality.Rule

import Universality.Percolation.CharacteristicAnnulus
import Universality.Percolation.CharacteristicIteration
import Universality.Percolation.FiniteCharacteristicGap
import Universality.Probability.CharacteristicFrequencyCover

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- Every frequency in the actual fundamental lattice interval is controlled
by a degree-iterated gap, with a quantitative integer scale for its magnitude. -/
theorem Classical.internal_mass_global_fourier_cover {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ bound : ℝ, 0 ≤ bound ∧ bound < 1 ∧ ∃ depth : ℕ, ∀ n ≥ depth, ∀ state t,
      1 ≤ |t| →
      |t| ≤ Real.pi * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n →
      ∃ k : ℕ,
        ‖(rule.generation n).network.conditionalVertexCharacteristic p state
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)‖ ≤
            bound ^ (rule.network.sourceIncidentEdges.card ^ k) ∧
        |t| ≤ Real.pi * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (k + 1) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  obtain ⟨annulusBound, ha0, ha1, hevent⟩ :=
    h.internal_mass_characteristic_annulus p hp hp' hfixed 1 radius zero_lt_one hradius.le
  obtain ⟨start, hstart⟩ := eventually_atTop.mp hevent
  let depth := max start 1
  have hdepth : 1 ≤ depth := le_max_right _ _
  have hcutoff : 0 < 1 / radius ^ depth := one_div_pos.mpr (pow_pos hradius0 _)
  have hcutoffPi : 1 / radius ^ depth ≤ Real.pi := by
    have hle : 1 / radius ^ depth ≤ 1 := (div_le_one (pow_pos hradius0 _)).mpr (one_le_pow₀ hradius.le)
    linarith [Real.two_le_pi]
  obtain ⟨baseBound, hb0, hb1, hbase⟩ :=
    h.internal_mass_base_frequency_gap p hp hp' hfixed (1 / radius ^ depth) hcutoff hcutoffPi
  let bound := max annulusBound baseBound
  have hbound0 : 0 ≤ bound := ha0.trans (le_max_left _ _)
  have hbound1 : bound < 1 := max_lt ha1 hb1
  refine ⟨bound, hbound0, hbound1, depth, ?_⟩
  intro n hn state t ht htpi
  let u := t / radius ^ n
  have hunorm : |u| * radius ^ n = |t| := by
    dsimp [u]
    rw [abs_div, abs_of_pos (pow_pos hradius0 _), div_mul_cancel₀ _ (pow_ne_zero _ hradius0.ne')]
  have hupi : |u| ≤ Real.pi := by
    apply (mul_le_mul_iff_left₀ (pow_pos hradius0 n)).mp
    rw [hunorm]
    exact htpi
  obtain ⟨k, hk, hkt⟩ := characteristic_frequency_cover
    (fun m child frequency => ‖(rule.generation m).network.conditionalVertexCharacteristic p child frequency‖)
    radius bound rule.network.sourceIncidentEdges.card depth hradius hdepth
    (fun child frequency hlow hhigh =>
      (hbase child frequency ((div_le_iff₀ (pow_pos hradius0 depth)).mpr hlow) hhigh).trans (le_max_right _ _))
    (by
      intro m hm child frequency hlow hhigh
      have hgap := hstart m ((le_max_left start 1).trans hm) child (frequency * radius ^ m)
        (by simpa only [abs_mul, abs_of_pos (pow_pos hradius0 m)] using hlow)
        (by simpa only [abs_mul, abs_of_pos (pow_pos hradius0 m)] using hhigh)
      have heq : frequency * radius ^ m / radius ^ m = frequency := mul_div_cancel_right₀ _ (pow_ne_zero _ hradius0.ne')
      rw [heq] at hgap
      exact hgap.trans (le_max_left _ _))
    (fun m frequency hvalues extra child =>
      rule.generation_characteristic_norm_iterate h.massAdmissible.symmetric p hp hp' hfixed
        m frequency bound hbound0 hbound1.le hvalues extra child)
    n hn state u (by rwa [hunorm]) hupi
  exact ⟨k, hk, by rwa [hunorm] at hkt⟩

end
end Universality.Rule

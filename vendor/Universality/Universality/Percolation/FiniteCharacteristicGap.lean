import Universality.Percolation.FiniteCharacteristicAperiodic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Universality
noncomputable section

theorem exp_real_phase_ne_one_of_abs_le_pi (t : ℝ) (ht : t ≠ 0) (hpi : |t| ≤ Real.pi) :
    Complex.exp ((t : ℂ) * Complex.I) ≠ 1 := by
  have hpositive (s : ℝ) (hs : 0 ≤ s) (hsPi : s ≤ Real.pi) (hsNe : s ≠ 0) :
      Complex.exp ((s : ℂ) * Complex.I) ≠ 1 := by
    intro heq
    have hinj := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (x := (s : ℂ) * Complex.I) (y := 0)
      (by simpa using (neg_neg_of_pos Real.pi_pos).trans_le hs)
      (by simpa using hsPi) (by simpa using neg_neg_of_pos Real.pi_pos)
      (by simpa using Real.pi_pos.le) (by simpa using heq)
    exact hsNe (by simpa using congrArg Complex.im hinj)
  by_cases hnonnegative : 0 ≤ t
  · exact hpositive t hnonnegative (by simpa only [abs_of_nonneg hnonnegative] using hpi) ht
  · have hnegative : t ≤ 0 := (lt_of_not_ge hnonnegative).le
    intro heq
    apply hpositive (-t) (neg_nonneg.mpr hnegative)
      (by simpa only [abs_of_nonpos hnegative] using hpi) (neg_ne_zero.mpr ht)
    rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, heq, inv_one]

end
end Universality

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

theorem continuous_conditionalInternalCharacteristic (R : FiniteNetwork vertices edges)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) :
    Continuous (R.conditionalInternalCharacteristic p opened sourceSelected targetSelected) := by
  unfold conditionalInternalCharacteristic
  fun_prop

theorem continuous_conditionalVertexCharacteristic (R : FiniteNetwork vertices edges)
    (p : ℝ) (state : LiveState) : Continuous (R.conditionalVertexCharacteristic p state) :=
  R.continuous_conditionalInternalCharacteristic p _ _ _

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- Uniform aperiodicity of the actual second-depth characteristic functions
on any compact subannulus of the fundamental lattice-frequency interval. -/
theorem Classical.internal_mass_base_frequency_gap {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (lower : ℝ) (hlower : 0 < lower) (hlowerPi : lower ≤ Real.pi) :
    ∃ bound : ℝ, 0 ≤ bound ∧ bound < 1 ∧ ∀ state t,
      lower ≤ |t| → |t| ≤ Real.pi →
      ‖(rule.generation 1).network.conditionalVertexCharacteristic p state t‖ ≤ bound := by
  let characteristic (state : LiveState) := (rule.generation 1).network.conditionalVertexCharacteristic p state
  let maximum (t : ℝ) := max ‖characteristic .connected t‖
    (max ‖characteristic .both t‖ ‖characteristic .single t‖)
  have hcontinuous (state : LiveState) : Continuous (characteristic state) :=
    (rule.generation 1).network.continuous_conditionalVertexCharacteristic p state
  have hmaximumContinuous : Continuous maximum :=
    (hcontinuous .connected).norm.max ((hcontinuous .both).norm.max (hcontinuous .single).norm)
  let annulus := Set.Icc lower Real.pi ∪ Set.Icc (-Real.pi) (-lower)
  have hcompact : IsCompact annulus := isCompact_Icc.union isCompact_Icc
  have hnonempty : annulus.Nonempty := ⟨lower, Or.inl ⟨le_rfl, hlowerPi⟩⟩
  obtain ⟨point, hpoint, hmax⟩ := hcompact.exists_isMaxOn hnonempty hmaximumContinuous.continuousOn
  have hpointNe : point ≠ 0 := by
    rcases hpoint with hpos | hneg
    · exact ne_of_gt (hlower.trans_le hpos.1)
    · exact ne_of_lt (hneg.2.trans_lt (neg_neg_of_pos hlower))
  have hpointPi : |point| ≤ Real.pi := by
    rcases hpoint with hpos | hneg
    · rw [abs_of_nonneg (hlower.le.trans hpos.1)]; exact hpos.2
    · rw [abs_of_nonpos (hneg.2.trans (neg_nonpos.mpr hlower.le))]; linarith [hneg.1]
  have hstrict (state : LiveState) : ‖characteristic state point‖ < 1 :=
    h.internal_mass_base_characteristic_strict p hp hp' hfixed point
      (exp_real_phase_ne_one_of_abs_le_pi point hpointNe hpointPi) state
  refine ⟨maximum point, (norm_nonneg _).trans (le_max_left _ _),
    max_lt (hstrict .connected) (max_lt (hstrict .both) (hstrict .single)), ?_⟩
  intro state t htLower htUpper
  have htAnnulus : t ∈ annulus := by
    rcases le_total 0 t with hpos | hneg
    · exact Or.inl (by simpa only [Set.mem_Icc, abs_of_nonneg hpos] using And.intro htLower htUpper)
    · apply Or.inr
      simp only [Set.mem_Icc]
      rw [abs_of_nonpos hneg] at htLower htUpper
      constructor <;> linarith
  have hstate : ‖characteristic state t‖ ≤ maximum t := by
    cases state
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  exact hstate.trans (hmax htAnnulus)

end
end Universality.Rule

import Universality.Percolation.AllTypesMassNonlattice

namespace Universality
noncomputable section
open MeasureTheory Filter

theorem continuous_randomCharacteristic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) : Continuous (randomCharacteristic μ f) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t
    exact (integrable_characteristic_kernel hf t).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall (fun x => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl])
  · exact integrable_const _
  · exact Eventually.of_forall (fun x => by fun_prop)

end
end Universality

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- On every fixed annulus away from zero, all three actual normalized
finite-depth characteristic functions are eventually bounded away from one. -/
theorem Classical.internal_mass_characteristic_annulus {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : lower ≤ upper) :
    ∃ bound : ℝ, 0 ≤ bound ∧ bound < 1 ∧ ∀ᶠ n : ℕ in atTop, ∀ (state : LiveState) (t : ℝ),
      lower ≤ |t| → |t| ≤ upper →
      ‖(rule.generation n).network.conditionalInternalCharacteristic p (state == .connected)
        true (state == .both)
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)‖ ≤ bound := by
  obtain ⟨limit, hmem, hstrict, huniform⟩ := h.internal_vertex_mass_nonlattice_limits p hp hp' hfixed
  let characteristic (state : LiveState) := charFun
    ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state))
  let maximum (t : ℝ) := max ‖characteristic .connected t‖
    (max ‖characteristic .both t‖ ‖characteristic .single t‖)
  have hcontinuous (state : LiveState) : Continuous (characteristic state) := by
    have heq : characteristic state = randomCharacteristic
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) (limit state) :=
      funext (fun t => (randomCharacteristic_eq_charFun_map (hmem state).aestronglyMeasurable t).symm)
    rw [heq]
    exact continuous_randomCharacteristic _ (hmem state).aestronglyMeasurable
  have hmaximumContinuous : Continuous maximum :=
    (hcontinuous .connected).norm.max ((hcontinuous .both).norm.max (hcontinuous .single).norm)
  let annulus := Set.Icc lower upper ∪ Set.Icc (-upper) (-lower)
  have hcompact : IsCompact annulus := isCompact_Icc.union isCompact_Icc
  have hnonempty : annulus.Nonempty := ⟨lower, Or.inl ⟨le_rfl, hupper⟩⟩
  obtain ⟨point, hpoint, hmax⟩ := hcompact.exists_isMaxOn hnonempty hmaximumContinuous.continuousOn
  have hpointNe : point ≠ 0 := by
    rcases hpoint with hpos | hneg
    · exact ne_of_gt (hlower.trans_le hpos.1)
    · exact ne_of_lt (hneg.2.trans_lt (neg_neg_of_pos hlower))
  have hmaxLt : maximum point < 1 :=
    max_lt (hstrict .connected point hpointNe)
      (max_lt (hstrict .both point hpointNe) (hstrict .single point hpointNe))
  have hmaxNonneg : 0 ≤ maximum point := (norm_nonneg _).trans (le_max_left _ _)
  let error := (1 - maximum point) / 2
  let bound := (1 + maximum point) / 2
  have herror : 0 < error := by dsimp [error]; linarith
  refine ⟨bound, ?_, ?_, ?_⟩
  · dsimp [bound]; linarith
  · dsimp [bound]; linarith
  have hevent : ∀ᶠ n : ℕ in atTop, ∀ state t, |t| ≤ upper →
      dist (characteristic state t)
        ((rule.generation n).network.conditionalInternalCharacteristic p (state == .connected)
          true (state == .both)
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)) < error := by
    apply Filter.eventually_all.mpr
    intro state
    exact Metric.tendstoUniformlyOn_iff.mp (huniform state upper) error herror
  filter_upwards [hevent] with n hn
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
  have hlimitBound := hstate.trans (hmax htAnnulus)
  have herrorBound := hn state t htUpper
  let finiteValue := (rule.generation n).network.conditionalInternalCharacteristic p (state == .connected)
    true (state == .both)
    (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
  change ‖finiteValue‖ ≤ bound
  apply le_of_lt
  calc
    ‖finiteValue‖ = ‖(finiteValue - characteristic state t) + characteristic state t‖ := by rw [sub_add_cancel]
    _ ≤ ‖finiteValue - characteristic state t‖ + ‖characteristic state t‖ := norm_add_le _ _
    _ < error + maximum point := add_lt_add_of_lt_of_le
      (by simpa only [dist_eq_norm, norm_sub_rev] using herrorBound) hlimitBound
    _ = bound := by dsimp [error, bound]; ring

end
end Universality.Rule

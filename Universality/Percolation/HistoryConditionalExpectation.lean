import Universality.Percolation.InfiniteMassMoments
import Universality.Probability.TrajectoryConditionalExpectation

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem integrable_infiniteLaw_observable (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory n → ℝ) :
    Integrable (fun path => observable (path n)) (infiniteLaw rule p hp hp' hfixed opened) :=
  (memLp_infiniteLaw_observable rule p hp hp' hfixed opened n observable 1).integrable le_rfl

theorem integral_transition (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ) (history : rule.ConfigurationHistory n)
    (observable : rule.ConfigurationHistory (n + 1) → ℝ) :
    ∫ next, observable next ∂transition rule p hp hp' hfixed n history =
      ∑ fine, refinementWeight rule p n (latest rule n history) fine * observable (history, fine) := by
  classical
  change ∫ next, observable next ∂(finiteWeightPMF _ _ _).toMeasure = _
  rw [PMF.integral_eq_sum]
  simp only [finiteWeightPMF_apply, ENNReal.toReal_ofReal
    (extensionWeight_nonneg rule p hp.le hp'.le n history _), smul_eq_mul]
  change (∑ next : rule.ConfigurationHistory n × Configuration (rule.generation (n + 1)).edges,
    (if next.1 = history then refinementWeight rule p n (latest rule n history) next.2 else 0) *
      observable next) = _
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem infiniteLaw_condExp (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory (n + 1) → ℝ) :
    (infiniteLaw rule p hp hp' hfixed opened)[fun path => observable (path (n + 1)) | Filtration.piLE n]
      =ᵐ[infiniteLaw rule p hp hp' hfixed opened] fun path =>
        ∑ fine, refinementWeight rule p n (latest rule n (path n)) fine * observable (path n, fine) := by
  letI := law_probability rule p hp hp' hfixed opened 0
  letI : Nonempty (rule.ConfigurationHistory (n + 1)) := ⟨ofFine rule (n + 1) (fun _ => false)⟩
  have h := markovTrajectory_condExp (law rule p hp hp' hfixed opened 0)
    (transition rule p hp hp' hfixed) n observable (measurable_of_countable observable).stronglyMeasurable
    (integrable_infiniteLaw_observable rule p hp hp' hfixed opened (n + 1) observable)
  exact h.trans (Filter.Eventually.of_forall (fun path =>
    integral_transition rule p hp hp' hfixed n (path n) observable))

theorem history_observables_stronglyAdapted (rule : Rule)
    (observable : ∀ n, rule.ConfigurationHistory n → ℝ) :
    StronglyAdapted Filtration.piLE (fun n path => observable n (path n)) := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have h := ((measurable_of_countable (observable n)).comp
    (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n))).comp
    (Measurable.of_comap_le le_rfl :
      @Measurable _ _ (MeasurableSpace.comap (Preorder.frestrictLe n) MeasurableSpace.pi)
        _ (Preorder.frestrictLe n))
  exact h.stronglyMeasurable

theorem integral_refinement_observable (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory (n + 1) → ℝ) :
    (∫ path, ∑ fine, refinementWeight rule p n (latest rule n (path n)) fine *
        observable (path n, fine) ∂infiniteLaw rule p hp hp' hfixed opened) =
      ∫ path, observable (path (n + 1)) ∂infiniteLaw rule p hp hp' hfixed opened := by
  rw [← integral_congr_ae (infiniteLaw_condExp rule p hp hp' hfixed opened n observable)]
  exact integral_condExp (Filtration.piLE.le n)

end
end Universality.Rule.ConfigurationHistory

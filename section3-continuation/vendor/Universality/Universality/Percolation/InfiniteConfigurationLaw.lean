import Universality.Percolation.HistoryTransition
import Universality.Probability.MarkovTrajectory

/-! A common probability space for all conditioned percolation histories. -/

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators

def infiniteLaw (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) :
    Measure (Π n, rule.ConfigurationHistory n) :=
  markovTrajectory (law rule p hp hp' hfixed opened 0) (transition rule p hp hp' hfixed)

instance infiniteLaw_probability (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) :
    IsProbabilityMeasure (infiniteLaw rule p hp hp' hfixed opened) := by
  letI := law_probability rule p hp hp' hfixed opened 0
  letI : ∀ n, IsMarkovKernel (transition rule p hp hp' hfixed n) :=
    transition_markov rule p hp hp' hfixed
  unfold infiniteLaw
  infer_instance

theorem infiniteLaw_marginal (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ) :
    (infiniteLaw rule p hp hp' hfixed opened).map (fun path => path n) =
      law rule p hp hp' hfixed opened n := by
  letI := law_probability rule p hp hp' hfixed opened 0
  exact markovTrajectory_marginal (law rule p hp hp' hfixed opened)
    (transition rule p hp hp' hfixed) (transition_law rule p hp hp' hfixed opened) n

/-- Every complete finite history has exactly its previously computed weight. -/
theorem infiniteLaw_history_atom (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (history : rule.ConfigurationHistory n) :
    infiniteLaw rule p hp hp' hfixed opened {path | path n = history} =
      ENNReal.ofReal (recursiveWeight rule p opened n history) := by
  have h := congrArg (fun μ : Measure (rule.ConfigurationHistory n) => μ {history})
    (infiniteLaw_marginal rule p hp hp' hfixed opened n)
  rw [Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _)] at h
  exact h.trans (finiteWeightPMF_singleton _ _ _ _)

theorem law_coherent (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ) :
    ∀ᵐ history ∂law rule p hp hp' hfixed opened n, coherent rule n history := by
  apply ae_iff_of_countable.mpr
  intro history hpositive
  by_contra hnot
  apply hpositive
  change (finiteWeightPMF _ _ _).toMeasure {history} = 0
  rw [finiteWeightPMF_singleton, recursiveWeight_eq_directWeight rule p hp hp' hfixed]
  simp [directWeight, hnot]

theorem infiniteLaw_coherent (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂infiniteLaw rule p hp hp' hfixed opened, ∀ n, coherent rule n (path n) := by
  apply ae_all_iff.mpr
  intro n
  have h := law_coherent rule p hp hp' hfixed opened n
  rw [← infiniteLaw_marginal rule p hp hp' hfixed opened n] at h
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable h

theorem transition_extends (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (n : ℕ) (history : rule.ConfigurationHistory n) :
    ∀ᵐ next ∂transition rule p hp hp' hfixed n history, next.1 = history := by
  apply ae_iff_of_countable.mpr
  intro next hpositive
  by_contra hnot
  apply hpositive
  change finiteWeightKernel _ _ _ history {next} = 0
  rw [finiteWeightKernel_singleton]
  simp [extensionWeight, hnot]

theorem infiniteLaw_extends (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂infiniteLaw rule p hp hp' hfixed opened, ∀ n, (path (n + 1)).1 = path n := by
  apply ae_all_iff.mpr
  intro n
  letI := law_probability rule p hp hp' hfixed opened 0
  apply markovTrajectory_step_ae (law rule p hp hp' hfixed opened 0)
    (transition rule p hp hp' hfixed) n (fun history next => next.1 = history)
  · exact Set.to_countable _ |>.measurableSet
  · exact transition_extends rule p hp hp' hfixed n

/-- The finest configurations coarsen consistently at all levels, simultaneously. -/
theorem infiniteLaw_coarsens (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂infiniteLaw rule p hp hp' hfixed opened, ∀ n,
      rule.coarsenGeneration n (latest rule (n + 1) (path (n + 1))) =
        latest rule n (path n) := by
  filter_upwards [infiniteLaw_coherent rule p hp hp' hfixed opened,
    infiniteLaw_extends rule p hp hp' hfixed opened] with path hcoherent hextends
  intro n
  have h := (hcoherent (n + 1)).2
  rw [hextends n] at h
  exact h

end
end Universality.Rule.ConfigurationHistory

import Universality.Percolation.InfiniteObservables

namespace Universality.Rule.ConfigurationHistory
noncomputable section
open FiniteNetwork MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem law_terminal_condition (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ) :
    ∀ᵐ history ∂law rule p hp hp' hfixed opened n,
      (rule.generation n).network.crosses (latest rule n history) = opened := by
  apply ae_iff_of_countable.mpr
  intro history hpositive
  by_contra hnot
  apply hpositive
  change (finiteWeightPMF _ _ _).toMeasure {history} = 0
  rw [finiteWeightPMF_singleton, recursiveWeight_eq_directWeight rule p hp hp' hfixed]
  simp [directWeight, conditionalCellWeight, hnot]

theorem infiniteLaw_terminal_condition (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂infiniteLaw rule p hp hp' hfixed opened, ∀ n,
      (rule.generation n).network.crosses (latest rule n (path n)) = opened := by
  apply ae_all_iff.mpr
  intro n
  have h := law_terminal_condition rule p hp hp' hfixed opened n
  rw [← infiniteLaw_marginal rule p hp hp' hfixed opened n] at h
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable h

end
end Universality.Rule.ConfigurationHistory

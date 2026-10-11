import Universality.Percolation.OrientedStates

namespace Universality.Rule
noncomputable section
open FiniteNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

@[reducible] def LabelHistory (rule : Rule) : ℕ → Type
  | 0 => Fin rule.edges → OrientedState
  | n + 1 => rule.LabelHistory n × (Fin (rule.generation (n + 1)).edges → OrientedState)

def LabelHistory.latest (rule : Rule) :
    (n : ℕ) → rule.LabelHistory n → Fin (rule.generation n).edges → OrientedState
  | 0, history => history
  | _ + 1, history => history.2

/-- Labels read directly from the actual source cluster at every generation. -/
def ConfigurationHistory.globalLabels (rule : Rule) :
    (n : ℕ) → rule.ConfigurationHistory n → rule.LabelHistory n
  | 0, history => rule.network.orientedChildState true false history
  | n + 1, history =>
    (globalLabels rule n history.1,
      (rule.generation (n + 1)).network.orientedChildState true false history.2)

/-- Labels obtained locally, retaining the active terminal of every child.
The complete within-cell configuration is sampled as one object. -/
def ConfigurationHistory.recursiveLabels (rule : Rule) :
    (n : ℕ) → rule.ConfigurationHistory n → rule.LabelHistory n
  | 0, history => rule.network.orientedChildState true false history
  | n + 1, history =>
    (recursiveLabels rule n history.1, fun edge =>
      let pair := finProdFinEquiv.symm edge
      let parent := LabelHistory.latest rule n (recursiveLabels rule n history.1) pair.1
      rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (substitutionConfigurationEquiv.symm history.2 pair.1) pair.2)

theorem ConfigurationHistory.globalLabels_latest (rule : Rule) (n : ℕ)
    (history : rule.ConfigurationHistory n) :
    LabelHistory.latest rule n (globalLabels rule n history) =
      (rule.generation n).network.orientedChildState true false (latest rule n history) := by
  cases n <;> rfl

/-- The entire labelled cell structure agrees pathwise on every coherent
history, not only in its expected counts. -/
theorem ConfigurationHistory.recursiveLabels_eq_globalLabels (rule : Rule)
    (n : ℕ) (history : rule.ConfigurationHistory n) (hcoherent : coherent rule n history) :
    recursiveLabels rule n history = globalLabels rule n history := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases history with ⟨history, fine⟩
    obtain ⟨hpast, hcoarse⟩ := hcoherent
    simp only [recursiveLabels, globalLabels, ih history hpast]
    congr 1
    funext edge
    rw [globalLabels_latest]
    have h := (rule.generation n).network.orientedChildState_substitute rule.network
      true false (substitutionConfigurationEquiv.symm fine)
      (finProdFinEquiv.symm edge).1 (finProdFinEquiv.symm edge).2
    have hpair : finProdFinEquiv ((finProdFinEquiv.symm edge).1,
        (finProdFinEquiv.symm edge).2) = edge := Equiv.apply_symm_apply _ edge
    rw [hpair, Equiv.apply_symm_apply] at h
    change rule.network.coarseConfiguration (substitutionConfigurationEquiv.symm fine) =
      latest rule n history at hcoarse
    rw [hcoarse] at h
    exact h.symm

/-- The finite-depth random EIGS has the complete joint law of the labelled
critical Bernoulli cluster. Arbitrary observables include simultaneous events
at different levels and correlations between siblings. -/
theorem critical_randomEIGS_joint_law (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (observable : rule.LabelHistory n → ℝ) :
    (∑ history, ConfigurationHistory.recursiveWeight rule p true n history *
      observable (ConfigurationHistory.recursiveLabels rule n history)) =
      ∑ fine, (rule.generation n).network.conditionalCellWeight p true fine *
        observable (ConfigurationHistory.globalLabels rule n
          (ConfigurationHistory.ofFine rule n fine)) := by
  rw [ConfigurationHistory.joint_observable_law rule p hp hp' hfixed true n]
  apply Finset.sum_congr rfl
  intro fine _
  rw [ConfigurationHistory.recursiveLabels_eq_globalLabels rule n _]
  apply (ConfigurationHistory.coherent_iff_ofFine rule n _).mpr
  rw [ConfigurationHistory.latest_ofFine]

theorem critical_randomEIGS_extracts_cluster (rule : Rule) (n : ℕ)
    (fine : Configuration (rule.generation n).edges) (edge : Fin (rule.generation n).edges) :
    LabelHistory.latest rule n
      (ConfigurationHistory.recursiveLabels rule n (ConfigurationHistory.ofFine rule n fine)) edge =
        .connected ↔
      fine edge = true ∧ ((rule.generation n).network.openGraph fine).Reachable
        (rule.generation n).network.source ((rule.generation n).network.endpoint edge).1 := by
  have hcoherent : ConfigurationHistory.coherent rule n
      (ConfigurationHistory.ofFine rule n fine) := by
    apply (ConfigurationHistory.coherent_iff_ofFine rule n _).mpr
    rw [ConfigurationHistory.latest_ofFine]
  rw [ConfigurationHistory.recursiveLabels_eq_globalLabels rule n _ hcoherent,
    ConfigurationHistory.globalLabels_latest, ConfigurationHistory.latest_ofFine]
  exact (rule.generation n).network.oriented_cluster_extraction fine edge

end
end Universality.Rule

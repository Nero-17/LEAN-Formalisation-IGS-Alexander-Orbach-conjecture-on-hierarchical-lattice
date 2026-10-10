import Universality.Percolation.JointDisintegration
import Universality.Graph.Iteration

/-!
# The complete finite-depth configuration law

Histories keep every generation, not just one marginal or an expected count.
Their direct law samples the finest Bernoulli configuration and coarsens it.
Their recursive law samples the coarse configuration then independently
refines its cells, conditioned on the prescribed individual crossing bits.
-/

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators

theorem substitute_crosses {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (ω : Fin outerEdges → Configuration innerEdges) :
    (R.substitute S).crosses (substitutionConfigurationEquiv ω) =
      R.crosses (S.coarseConfiguration ω) := by
  exact (R.substitute_conditioning S .connected ω).trans
    (R.substitutedConditioning_eq S .connected ω)

theorem conditional_substitution_joint_weight
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : S.reliability p = p)
    (opened : Bool) (coarse : Configuration outerEdges)
    (ω : Fin outerEdges → Configuration innerEdges) :
    R.conditionalCellWeight p opened coarse *
        (∏ e, S.conditionalCellWeight p (coarse e) (ω e)) =
      if S.coarseConfiguration ω = coarse then
        (R.substitute S).conditionalCellWeight p opened (substitutionConfigurationEquiv ω)
      else 0 := by
  classical
  rw [← S.critical_coarse_fiber_conditional_joint_weight p hfixed coarse ω]
  by_cases hcoarse : S.coarseConfiguration ω = coarse
  · subst coarse
    rw [if_pos rfl, if_pos rfl]
    unfold conditionalCellWeight
    rw [R.substitute_reliability S, hfixed, R.substitute_crosses S,
      bernoulliWeight_substitutionConfiguration]
    by_cases hroot : R.crosses (S.coarseConfiguration ω) = opened
    · simp only [if_pos hroot]
      rw [div_mul_div_comm]
      rw [mul_comm (if opened then R.reliability p else 1 - R.reliability p)]
      exact mul_div_mul_left _ _ (ne_of_gt (bernoulliWeight_pos hp hp' _))
    · simp [hroot]
  · simp [hcoarse]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork
open scoped BigOperators

@[reducible] def ConfigurationHistory (rule : Rule) : ℕ → Type
  | 0 => Configuration rule.edges
  | n + 1 => rule.ConfigurationHistory n × Configuration (rule.generation (n + 1)).edges

instance configurationHistoryFintype (rule : Rule) :
    (n : ℕ) → Fintype (rule.ConfigurationHistory n)
  | 0 => inferInstanceAs (Fintype (Configuration rule.edges))
  | n + 1 => by
    letI := configurationHistoryFintype rule n
    exact inferInstanceAs (Fintype (rule.ConfigurationHistory n ×
      Configuration (rule.generation (n + 1)).edges))

noncomputable instance configurationHistoryDecidableEq (rule : Rule) (n : ℕ) :
    DecidableEq (rule.ConfigurationHistory n) := Classical.decEq _

def ConfigurationHistory.latest (rule : Rule) :
    (n : ℕ) → rule.ConfigurationHistory n → Configuration (rule.generation n).edges
  | 0, history => history
  | _ + 1, history => history.2

def coarsenGeneration (rule : Rule) (n : ℕ)
    (ω : Configuration (rule.generation (n + 1)).edges) :
    Configuration (rule.generation n).edges :=
  rule.network.coarseConfiguration (substitutionConfigurationEquiv.symm ω)

def ConfigurationHistory.coherent (rule : Rule) :
    (n : ℕ) → rule.ConfigurationHistory n → Prop
  | 0, _ => True
  | n + 1, history =>
    ConfigurationHistory.coherent rule n history.1 ∧
      rule.coarsenGeneration n history.2 = ConfigurationHistory.latest rule n history.1

def ConfigurationHistory.recursiveWeight (rule : Rule) (p : ℝ) (opened : Bool) :
    (n : ℕ) → rule.ConfigurationHistory n → ℝ
  | 0, history => rule.network.conditionalCellWeight p opened history
  | n + 1, history =>
    ConfigurationHistory.recursiveWeight rule p opened n history.1 *
      ∏ e, rule.network.conditionalCellWeight p
        (ConfigurationHistory.latest rule n history.1 e)
        (substitutionConfigurationEquiv.symm history.2 e)

def ConfigurationHistory.directWeight (rule : Rule) (p : ℝ) (opened : Bool)
    (n : ℕ) (history : rule.ConfigurationHistory n) : ℝ := by
  classical
  exact if ConfigurationHistory.coherent rule n history then
    (rule.generation n).network.conditionalCellWeight p opened
      (ConfigurationHistory.latest rule n history) else 0

/-- The history obtained by successively coarsening an actual finest-level
configuration. There is no additional randomness in the coarsening. -/
def ConfigurationHistory.ofFine (rule : Rule) :
    (n : ℕ) → Configuration (rule.generation n).edges → rule.ConfigurationHistory n
  | 0, fine => fine
  | n + 1, fine => (ofFine rule n (rule.coarsenGeneration n fine), fine)

theorem ConfigurationHistory.latest_ofFine (rule : Rule) (n : ℕ)
    (fine : Configuration (rule.generation n).edges) :
    latest rule n (ofFine rule n fine) = fine := by
  cases n <;> rfl

theorem ConfigurationHistory.coherent_iff_ofFine (rule : Rule) (n : ℕ)
    (history : rule.ConfigurationHistory n) :
    coherent rule n history ↔ ofFine rule n (latest rule n history) = history := by
  induction n with
  | zero => simp [coherent, ofFine, latest]
  | succ n ih =>
    rcases history with ⟨history, fine⟩
    simp only [coherent, latest, ofFine, Prod.mk.injEq, and_true]
    constructor
    · rintro ⟨h, hc⟩
      rw [hc]
      exact (ih history).mp h
    · intro h
      have hc := congrArg (latest rule n) h
      rw [latest_ofFine] at hc
      exact ⟨(ih history).mpr (by rwa [hc] at h), hc⟩

theorem ConfigurationHistory.sum_fine_atom (rule : Rule) (p : ℝ) (opened : Bool)
    (n : ℕ) (history : rule.ConfigurationHistory n) :
    (∑ fine : Configuration (rule.generation n).edges,
      if ofFine rule n fine = history then
        (rule.generation n).network.conditionalCellWeight p opened fine else 0) =
      directWeight rule p opened n history := by
  classical
  rw [Finset.sum_eq_single (latest rule n history)]
  · simp only [directWeight, coherent_iff_ofFine]
  · intro fine _ hne
    have h : ofFine rule n fine ≠ history := by
      intro heq
      have hf := congrArg (latest rule n) heq
      rw [latest_ofFine] at hf
      exact hne hf
    simp [h]
  · simp

/-- Equality of the full joint laws at every finite depth, under terminal
connection or disconnection. No symmetry or independence within a cell is
assumed. The only stationarity assumption is the actual reliability fixed point. -/
theorem ConfigurationHistory.recursiveWeight_eq_directWeight (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (opened : Bool) (n : ℕ) (history : rule.ConfigurationHistory n) :
    ConfigurationHistory.recursiveWeight rule p opened n history =
      ConfigurationHistory.directWeight rule p opened n history := by
  classical
  induction n with
  | zero => simp [recursiveWeight, directWeight, coherent, latest, generation]
  | succ n ih =>
    rcases history with ⟨history, fine⟩
    rw [recursiveWeight, ih]
    unfold directWeight
    by_cases hhistory : coherent rule n history
    · rw [if_pos hhistory]
      have h := conditional_substitution_joint_weight
        (rule.generation n).network rule.network p hp hp' hfixed opened
        (latest rule n history) (substitutionConfigurationEquiv.symm fine)
      have hg : (rule.generation (n + 1)).network =
          (rule.generation n).network.substitute rule.network := rfl
      rw [hg]
      simpa only [Equiv.apply_symm_apply, coherent, hhistory, true_and,
        coarsenGeneration, latest] using h
    · simp [hhistory, coherent]

/-- Arbitrary observables of the whole history have the same law. Indicators
may encode any simultaneous assignment of labels at any collection of levels. -/
theorem ConfigurationHistory.joint_observable_law (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (opened : Bool) (n : ℕ) (observable : rule.ConfigurationHistory n → ℝ) :
    (∑ history, recursiveWeight rule p opened n history * observable history) =
      ∑ fine, (rule.generation n).network.conditionalCellWeight p opened fine *
        observable (ofFine rule n fine) := by
  classical
  simp_rw [recursiveWeight_eq_directWeight rule p hp hp' hfixed,
    ← sum_fine_atom, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro fine _
  simp [ite_mul]

theorem ConfigurationHistory.sum_recursiveWeight (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (opened : Bool) (n : ℕ) :
    ∑ history, recursiveWeight rule p opened n history = 1 := by
  have h := joint_observable_law rule p hp hp' hfixed opened n (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  exact (rule.generation n).network.sum_conditionalCellWeight p
    (by rwa [rule.generation_fixed_point p hfixed])
    (by rwa [rule.generation_fixed_point p hfixed]) opened

theorem ConfigurationHistory.recursiveWeight_nonneg (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (opened : Bool) (n : ℕ) (history : rule.ConfigurationHistory n) :
    0 ≤ recursiveWeight rule p opened n history := by
  classical
  rw [recursiveWeight_eq_directWeight rule p hp hp' hfixed]
  unfold directWeight
  split
  · exact (rule.generation n).network.conditionalCellWeight_nonneg hp.le hp'.le _ _
  · exact le_rfl

end
end Universality.Rule

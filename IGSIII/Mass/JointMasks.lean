import IGSIII.Mass.ThreeStateMassPerron

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule.ConfigurationHistory

open FiniteNetwork Matrix MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology

/-- The conditioned crossing bit holds at every graph level on the original
infinite history space. -/
theorem infiniteLaw_crosses (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂infiniteLaw rule p positive below_one fixed_point opened, ∀ n,
      (rule.generation n).network.crosses (latest rule n (path n)) = opened := by
  apply ae_all_iff.mpr
  intro n
  have finite_crossing : ∀ᵐ history ∂law rule p positive below_one fixed_point opened n,
      (rule.generation n).network.crosses (latest rule n history) = opened := by
    apply ae_iff_of_countable.mpr
    intro history nonzero
    by_contra wrong_crossing
    apply nonzero
    change (finiteWeightPMF _ _ _).toMeasure {history} = 0
    rw [finiteWeightPMF_singleton, recursiveWeight_eq_directWeight rule p positive below_one fixed_point]
    simp [directWeight, FiniteNetwork.conditionalCellWeight, wrong_crossing]
  rw [← infiniteLaw_marginal rule p positive below_one fixed_point opened n] at finite_crossing
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable finite_crossing

/-- The target side keeps exactly the same raw graph configuration as its
source side and their B union; only the selected terminal mask changes. -/
noncomputable def targetVertexMass (rule : Rule) (n : ℕ)
    (path : Π k, rule.ConfigurationHistory k) : ℝ :=
  ((rule.generation n).network.internalSelectedMass false true (latest rule n (path n)) : ℝ)

/-- Exact disjoint-mask addition at every depth, simultaneously, on the
original noncrossing history law. No independent replacement side is sampled. -/
theorem both_vertexMass_joint_split (rule : Rule) (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∀ᵐ path ∂infiniteLaw rule p positive below_one fixed_point false, ∀ n,
      vertexMass rule .both n path = vertexMass rule .single n path + targetVertexMass rule n path := by
  filter_upwards [infiniteLaw_crosses rule p positive below_one fixed_point false] with path crossing
  intro n
  simp only [vertexMass, targetVertexMass, show (LiveState.both == LiveState.both) = true from rfl,
    show (LiveState.single == LiveState.both) = false from rfl]
  exact_mod_cast (rule.generation n).network.internalSelectedMass_disconnected
    (latest rule n (path n)) (crossing n)

end Universality.Rule.ConfigurationHistory

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- Both one-arm vertex limits exist on their original joint B history and
sum to the B limit. The target-side limit is obtained from the actual masked
count identity, not from a separate copy of a one-arm law. -/
theorem Classical.joint_both_mask_vertex_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ both source target : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp both 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point false) ∧
      MemLp source 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point false) ∧
      MemLp target 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point false) ∧
      (∀ path, both path = source path + target path) ∧
      ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point false,
        0 ≤ both path ∧ 0 ≤ source path ∧ 0 ≤ target path ∧
        (∀ n, ConfigurationHistory.vertexMass rule .both n path =
          ConfigurationHistory.vertexMass rule .single n path + ConfigurationHistory.targetVertexMass rule n path) ∧
        Tendsto (fun n : ℕ => ConfigurationHistory.vertexMass rule .both n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (both path)) ∧
        Tendsto (fun n : ℕ => ConfigurationHistory.vertexMass rule .single n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (source path)) ∧
        Tendsto (fun n : ℕ => ConfigurationHistory.targetVertexMass rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (target path)) := by
  obtain ⟨both, both_mem, both_convergence, _, _⟩ :=
    classicalRule.internal_vertex_mass_ae_L2_limit p positive below_one fixed_point .both
  obtain ⟨source, source_mem, source_convergence, _, _⟩ :=
    classicalRule.internal_vertex_mass_ae_L2_limit p positive below_one fixed_point .single
  refine ⟨both, source, both - source, both_mem, source_mem, both_mem.sub source_mem,
    fun path => by simp only [Pi.sub_apply]; ring, ?_⟩
  have radius_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive below_one
      fixed_point classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p
      positive below_one fixed_point classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  filter_upwards [both_convergence, source_convergence,
    ConfigurationHistory.both_vertexMass_joint_split rule p positive below_one fixed_point]
    with path both_convergence source_convergence split
  have target_convergence : Tendsto
      (fun n : ℕ => ConfigurationHistory.targetVertexMass rule n path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      atTop (𝓝 ((both - source) path)) := by
    change Tendsto _ atTop (𝓝 (both path - source path))
    convert both_convergence.sub source_convergence using 1
    ext n
    rw [split n]
    ring
  refine ⟨?_, ?_, ?_, split, both_convergence, source_convergence, target_convergence⟩
  · apply ge_of_tendsto' both_convergence
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg radius_positive.le n)
  · apply ge_of_tendsto' source_convergence
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg radius_positive.le n)
  · apply ge_of_tendsto' target_convergence
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg radius_positive.le n)

end Universality.Rule

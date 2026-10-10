import Universality.Graph.TerminalSpineProbability
import Universality.Percolation.MassSpectralLowerBound

namespace Universality.Rule
noncomputable section
open MeasureTheory Filter
open scoped Topology

/-- Every fixed vertex of every finite starting generation almost surely
escapes the two terminal positions in finitely many ancestral steps. -/
theorem Classical.ae_ancestral_stage_eventually_internal {rule : Rule} [NeZero rule.edges]
    (h : rule.Classical) (age : ℕ) (vertex : Fin (rule.generation age).vertices) :
    ∀ᵐ address ∂rule.ancestralSpineLaw, ∃ n : ℕ,
      rule.ancestralRootAtStage age n (vertex, address) ≠
        (rule.generation (age + n)).network.source ∧
      rule.ancestralRootAtStage age n (vertex, address) ≠
        (rule.generation (age + n)).network.target := by
  classical
  have hdegree := h.terminal_degree_spectral_bounds (1 / 2) (by norm_num) (by norm_num)
  have hm : (0 : ℝ) < rule.edges :=
    (Nat.cast_nonneg (rule.network.fullGraph.degree rule.network.source)).trans_lt
      (hdegree.2.1.trans hdegree.2.2)
  have hratio : (rule.network.fullGraph.degree rule.network.source : ℝ) / rule.edges < 1 :=
    (div_lt_one hm).mpr (hdegree.2.1.trans hdegree.2.2)
  have hdecay : Tendsto (fun n : ℕ =>
      2 * ((rule.network.fullGraph.degree rule.network.source : ℝ) / rule.edges) ^ n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (Nat.cast_nonneg _) hm.le) hratio).const_mul (2 : ℝ)
  let bad : Set (ℕ → Fin rule.edges) := {address | ¬ ∃ n : ℕ,
      rule.ancestralRootAtStage age n (vertex, address) ≠
        (rule.generation (age + n)).network.source ∧
      rule.ancestralRootAtStage age n (vertex, address) ≠
        (rule.generation (age + n)).network.target}
  have hbound (n : ℕ) : rule.ancestralSpineLaw.real bad ≤
      2 * ((rule.network.fullGraph.degree rule.network.source : ℝ) / rule.edges) ^ n := by
    apply (measureReal_mono (μ := rule.ancestralSpineLaw) (s₁ := bad)
      (s₂ := {address | rule.ancestralRootAtStage age n (vertex, address) =
          (rule.generation (age + n)).network.source ∨
        rule.ancestralRootAtStage age n (vertex, address) =
          (rule.generation (age + n)).network.target}) ?_).trans
      (h.ancestral_stage_boundary_probability_le age n vertex)
    intro address hbad
    by_contra hnot
    exact hbad ⟨n, not_or.mp hnot⟩
  have hzero : rule.ancestralSpineLaw.real bad = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hdecay
      (Eventually.of_forall hbound)) measureReal_nonneg
  apply ae_iff.mpr
  exact (measureReal_eq_zero_iff).mp hzero

end
end Universality.Rule

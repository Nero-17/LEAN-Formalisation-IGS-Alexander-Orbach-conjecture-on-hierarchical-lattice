import Universality.Graph.TerminalPrefixCounting
import Mathlib.MeasureTheory.Measure.Real

namespace Universality.Rule
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory FiniteNetwork

/-- Each terminal event is the exact uniform finite-prefix count divided
by the number of address words. -/
theorem ancestral_stage_terminal_probability_eq (rule : Rule) [NeZero rule.edges]
    (age n : ℕ) (vertex : Fin (rule.generation age).vertices) (side : Bool) :
    rule.ancestralSpineLaw.real
      {address | rule.ancestralRootAtStage age n (vertex, address) =
        (rule.generation (age + n)).network.terminalVertex side} =
      (rule.terminalPrefixCount age vertex n side : ℝ) / (rule.edges : ℝ) ^ n := by
  let event : Set (Fin n → Fin rule.edges) :=
    {word | rule.ancestralVertexPrefix age vertex n word =
      (rule.generation (age + n)).network.terminalVertex side}
  have hmeasurable : MeasurableSet event :=
    (measurable_of_countable (rule.ancestralVertexPrefix age vertex n)) (measurableSet_singleton _)
  have hprefix := Universality.finiteUniform_prefix_measurePreserving (α := Fin rule.edges) n
  have hmap := congrArg (fun measure : Measure (Fin n → Fin rule.edges) => measure event) hprefix.map_eq
  rw [Measure.map_apply hprefix.measurable hmeasurable] at hmap
  have hevent : (fun address : ℕ → Fin rule.edges => fun i : Fin n => address i.val) ⁻¹' event =
      {address | rule.ancestralRootAtStage age n (vertex, address) =
        (rule.generation (age + n)).network.terminalVertex side} := by
    ext address
    change rule.ancestralVertexPrefix age vertex n (fun i => address i.val) = _ ↔ _
    rw [rule.ancestralVertexPrefix_eq_stageRoot]
    rfl
  rw [hevent, PMF.toMeasure_uniformOfFintype_apply event hmeasurable] at hmap
  have hcard : Fintype.card event = rule.terminalPrefixCount age vertex n side := by
    simp only [event, Fintype.card_subtype, terminalPrefixCount, Finset.sum_boole, Nat.cast_id, Set.mem_setOf_eq]
  change (rule.ancestralSpineLaw _).toReal = _
  change (Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin rule.edges)).toMeasure) _).toReal = _
  rw [hmap, hcard]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

theorem Classical.ancestral_stage_terminal_probability_le {rule : Rule} [NeZero rule.edges]
    (h : rule.Classical) (age n : ℕ) (vertex : Fin (rule.generation age).vertices) (side : Bool) :
    rule.ancestralSpineLaw.real
      {address | rule.ancestralRootAtStage age n (vertex, address) =
        (rule.generation (age + n)).network.terminalVertex side} ≤
      ((rule.network.fullGraph.degree rule.network.source : ℝ) / rule.edges) ^ n := by
  rw [rule.ancestral_stage_terminal_probability_eq]
  calc
    _ ≤ ((rule.network.fullGraph.degree rule.network.source : ℝ) ^ n) / (rule.edges : ℝ) ^ n := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
      exact_mod_cast h.terminalPrefixCount_le age vertex n side
    _ = _ := (div_pow _ _ _).symm

/-- Both possible terminal outputs are counted. No one-step conditional
survival probability is assumed. -/
theorem Classical.ancestral_stage_boundary_probability_le {rule : Rule} [NeZero rule.edges]
    (h : rule.Classical) (age n : ℕ) (vertex : Fin (rule.generation age).vertices) :
    rule.ancestralSpineLaw.real
      {address | rule.ancestralRootAtStage age n (vertex, address) =
          (rule.generation (age + n)).network.source ∨
        rule.ancestralRootAtStage age n (vertex, address) =
          (rule.generation (age + n)).network.target} ≤
      2 * ((rule.network.fullGraph.degree rule.network.source : ℝ) / rule.edges) ^ n := by
  have hsource := h.ancestral_stage_terminal_probability_le age n vertex false
  have htarget := h.ancestral_stage_terminal_probability_le age n vertex true
  simp only [terminalVertex, Bool.false_eq_true, ↓reduceIte] at hsource htarget
  have hunion := measureReal_union_le (μ := rule.ancestralSpineLaw)
    {address | rule.ancestralRootAtStage age n (vertex, address) =
      (rule.generation (age + n)).network.source}
    {address | rule.ancestralRootAtStage age n (vertex, address) =
      (rule.generation (age + n)).network.target}
  exact hunion.trans (by linarith)

end
end Universality.Rule

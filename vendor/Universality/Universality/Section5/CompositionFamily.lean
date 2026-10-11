import Universality.Graph.ClassicalSubstitution
import Universality.Matrix.CommonPositiveVector
import Universality.Arithmetic.Commensurability

/-!
# Composing actual rules with a common critical mass eigenvector

The hypotheses below describe genuine finite networks.  The primitive
certificate-to-graph existence theorem is a separate obligation.
-/

namespace Universality.Section5
noncomputable section
open Matrix FiniteNetwork

def certificateWeight : LiveState → ℝ
  | .connected => 55
  | .both => 46
  | .single => 23

theorem certificateWeight_pos (state : LiveState) : 0 < certificateWeight state := by
  cases state <;> norm_num [certificateWeight]

/-- Exact responses of an actual classical rule, not a replacement graph definition. -/
structure RuleResponses (rule : Rule) (base : ℕ) : Prop where
  classical : rule.Classical
  fixed : rule.network.reliability (1 / 2) = 1 / 2
  distance : rule.network.fullGraph.dist rule.network.source rule.network.target = base ^ 100
  edges : rule.edges = base ^ 232
  thermal : deriv rule.network.reliability (1 / 2) = (base : ℝ) ^ 70
  mass : rule.network.massMatrix (1 / 2) *ᵥ certificateWeight =
    (base : ℝ) ^ 219 • certificateWeight

theorem RuleResponses.mul {outer inner : Rule} {outerBase innerBase : ℕ}
    (outerResponses : RuleResponses outer outerBase)
    (innerResponses : RuleResponses inner innerBase) :
    RuleResponses (outer * inner) (outerBase * innerBase) := by
  refine ⟨outerResponses.classical.mul innerResponses.classical, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Rule.mul_reliability, innerResponses.fixed, outerResponses.fixed]
  · change (outer.network.substitute inner.network).fullGraph.dist
      (outer.network.substitute inner.network).source
      (outer.network.substitute inner.network).target = _
    rw [FiniteNetwork.substitute_terminal_distance _ _
      (outerResponses.classical.connected _) (innerResponses.classical.connected _),
      outerResponses.distance, innerResponses.distance, mul_pow]
  · rw [Rule.mul_edges, outerResponses.edges, innerResponses.edges, mul_pow]
  · have composition : (outer * inner).network.reliability =
        outer.network.reliability ∘ inner.network.reliability :=
      funext (Rule.mul_reliability outer inner)
    rw [composition, deriv_comp _
      (outer.network.hasDerivAt_reliability _).differentiableAt
      (inner.network.hasDerivAt_reliability _).differentiableAt,
      innerResponses.fixed, outerResponses.thermal, innerResponses.thermal,
      Nat.cast_mul, mul_pow]
  · obtain ⟨symmetry, source, target⟩ := innerResponses.classical.massAdmissible.symmetric
    rw [Rule.mul_massMatrix outer inner (1 / 2)
      (by rw [innerResponses.fixed]; norm_num)
      (by rw [innerResponses.fixed]; norm_num) symmetry source target,
      innerResponses.fixed, Nat.cast_mul, mul_pow]
    exact common_eigenvector_mul _ _ _ _ _ outerResponses.mass innerResponses.mass

def compositionFamily (first repeated : Rule) : ℕ → Rule
  | 0 => first
  | index + 1 => compositionFamily first repeated index * repeated

theorem compositionFamily_responses {first repeated : Rule} {firstBase repeatedBase : ℕ}
    (firstResponses : RuleResponses first firstBase)
    (repeatedResponses : RuleResponses repeated repeatedBase) (index : ℕ) :
    RuleResponses (compositionFamily first repeated index) (firstBase * repeatedBase ^ index) := by
  induction index with
  | zero => simpa [compositionFamily] using firstResponses
  | succ index induction =>
    simpa [compositionFamily, pow_succ, Nat.mul_assoc] using induction.mul repeatedResponses

theorem RuleResponses.spectralRadius {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) :
    spectralRadius ℂ ((rule.network.massMatrix (1 / 2)).map Complex.ofReal) =
      ENNReal.ofReal ((base : ℝ) ^ 219) := by
  exact spectralRadius_eq_of_positive_eigenvector _ certificateWeight _
    (rule.network.massMatrix_nonneg (by norm_num) (by norm_num))
    certificateWeight_pos (by positivity) responses.mass

/-- Incommensurability for an actual family once its two primitive rules are supplied. -/
theorem compositionFamily_incommensurate {first repeated : Rule}
    (firstResponses : RuleResponses first 19)
    (repeatedResponses : RuleResponses repeated 661) {i j : ℕ} (different : i ≠ j) :
    ¬ ScaleCommensurate
      ((compositionFamily first repeated i).network.fullGraph.dist
        (compositionFamily first repeated i).network.source
        (compositionFamily first repeated i).network.target)
      ((compositionFamily first repeated j).network.fullGraph.dist
        (compositionFamily first repeated j).network.source
        (compositionFamily first repeated j).network.target) := by
  rw [(compositionFamily_responses firstResponses repeatedResponses i).distance,
      (compositionFamily_responses firstResponses repeatedResponses j).distance]
  exact explicit_scales_pairwise_incommensurate different

end
end Universality.Section5

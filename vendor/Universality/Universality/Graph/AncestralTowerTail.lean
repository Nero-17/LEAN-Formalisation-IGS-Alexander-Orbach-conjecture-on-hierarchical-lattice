import Universality.Graph.TowerTail
import Universality.Graph.AncestralStageRootLaw

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

theorem ancestralTower_tail (rule : Rule) (age start : ℕ) (address : ℕ → Fin rule.edges) :
    (rule.ancestralTower age address).tail start =
      rule.ancestralTower (age + start) (fun n => address (start + n)) := by
  unfold NetworkTower.tail ancestralTower
  congr! 2 <;> simp only [Nat.add_assoc]
  subst_vars
  congr 1
  omega

/-- Discarding finitely many iid ancestral choices preserves their actual law. -/
theorem ancestralSpine_shift_measurePreserving (rule : Rule) [NeZero rule.edges]
    (start : ℕ) :
    MeasurePreserving (fun address : ℕ → Fin rule.edges => fun n => address (start + n))
      rule.ancestralSpineLaw rule.ancestralSpineLaw := by
  refine ⟨measurable_pi_lambda _ (fun n => measurable_pi_apply (start + n)), ?_⟩
  unfold ancestralSpineLaw
  exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ heq => Nat.add_left_cancel heq)

/-- Stage-zero eventual interior status in the shifted physical ancestry is
exactly the status needed at an arbitrary finite stage of the original tower. -/
theorem ancestralTail_eventually_internal_iff (rule : Rule) (age start : ℕ)
    (address : ℕ → Fin rule.edges) :
    (∀ vertex : Fin (rule.generation (age + start)).vertices, ∃ n,
      ((rule.ancestralTower age address).tail start).vertexMap 0 n (Nat.zero_le n) vertex ≠
          (((rule.ancestralTower age address).tail start).stage n).network.source ∧
      ((rule.ancestralTower age address).tail start).vertexMap 0 n (Nat.zero_le n) vertex ≠
          (((rule.ancestralTower age address).tail start).stage n).network.target) ↔
    (∀ vertex : Fin (rule.generation (age + start)).vertices, ∃ n,
      rule.ancestralRootAtStage (age + start) n (vertex, fun k => address (start + k)) ≠
          (rule.generation ((age + start) + n)).network.source ∧
      rule.ancestralRootAtStage (age + start) n (vertex, fun k => address (start + k)) ≠
          (rule.generation ((age + start) + n)).network.target) := by
  change ((rule.ancestralTower age address).tail start).RootEventuallyInternal ↔
    (rule.ancestralTower (age + start) (fun n => address (start + n))).RootEventuallyInternal
  rw [rule.ancestralTower_tail]

end
end Universality.Rule

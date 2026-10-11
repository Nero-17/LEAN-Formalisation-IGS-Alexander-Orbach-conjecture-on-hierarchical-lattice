import Universality.Graph.UniformRootRadiusIdentification
import Universality.Percolation.RadiusPointLaw

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem radius_point_event_iff (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (radius : ℕ) :
    (tower.radiusTailEvent configuration root radius ∧
      ¬ tower.radiusTailEvent configuration root (radius + 1)) ↔
    ((∃ vertex, (tower.openGraph configuration).Reachable (tower.vertex 0 root) vertex ∧
        (tower.openGraph (fun _ => true)).dist (tower.vertex 0 root) vertex = radius) ∧
      ∀ vertex, (tower.openGraph configuration).Reachable (tower.vertex 0 root) vertex →
        (tower.openGraph (fun _ => true)).dist (tower.vertex 0 root) vertex ≤ radius) := by
  constructor
  · rintro ⟨⟨vertex, hreach, hlower⟩, hnot⟩
    have hupper : ∀ other, (tower.openGraph configuration).Reachable (tower.vertex 0 root) other →
        (tower.openGraph (fun _ => true)).dist (tower.vertex 0 root) other ≤ radius := by
      intro other hother
      by_contra hlarge
      exact hnot ⟨other, hother, by omega⟩
    exact ⟨⟨vertex, hreach, Nat.le_antisymm (hupper vertex hreach) hlower⟩, hupper⟩
  · rintro ⟨⟨vertex, hreach, heq⟩, hupper⟩
    refine ⟨⟨vertex, hreach, heq.ge⟩, ?_⟩
    rintro ⟨other, hother, hlarge⟩
    have := hupper other hother
    omega

end
end Universality.NetworkTower

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def uniformRootRadiusPointEvent (rule : Rule) (radius : ℕ) (sample : rule.UniformRootSample) : Prop :=
  rule.uniformRootRadiusTailEvent radius sample ∧ ¬ rule.uniformRootRadiusTailEvent (radius + 1) sample

def uniformRootRadiusProbability (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (p : unitInterval) (radius : ℕ) : ℝ :=
  (rule.uniformRootSampleLaw hedges p).real {sample | rule.uniformRootRadiusPointEvent radius sample}

theorem uniformRootRadiusTailEvent_antitone (rule : Rule) :
    Antitone (fun radius => {sample | rule.uniformRootRadiusTailEvent radius sample}) := by
  intro first last hle sample hsample
  obtain ⟨vertex, hreach, hradius⟩ := hsample
  exact ⟨vertex, hreach, hle.trans hradius⟩

theorem Classical.measurableSet_uniformRootRadiusPointEvent {rule : Rule} (h : rule.Classical)
    (radius : ℕ) : MeasurableSet {sample | rule.uniformRootRadiusPointEvent radius sample} :=
  (h.measurableSet_uniformRootRadiusTailEvent radius).inter
    (h.measurableSet_uniformRootRadiusTailEvent (radius + 1)).compl

theorem Classical.uniformRootRadiusProbability_eq_tail_difference {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (radius : ℕ) :
    rule.uniformRootRadiusProbability h.edges_gt_one p radius =
      rule.uniformRootRadiusTailProbability h.edges_gt_one p radius -
        rule.uniformRootRadiusTailProbability h.edges_gt_one p (radius + 1) :=
  measureReal_sdiff (rule.uniformRootRadiusTailEvent_antitone (Nat.le_succ radius))
    (h.measurableSet_uniformRootRadiusTailEvent (radius + 1))

theorem Classical.uniformRootRadiusProbability_eq_limiting {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (hfixed : rule.network.reliability (p : ℝ) = p) (radius : ℕ) :
    rule.uniformRootRadiusProbability h.edges_gt_one p radius =
      rule.limitingRootRadiusProbability (p : ℝ) radius := by
  rw [h.uniformRootRadiusProbability_eq_tail_difference,
    h.uniformRootRadiusTailProbability_eq_limiting p hp hp' hfixed,
    h.uniformRootRadiusTailProbability_eq_limiting p hp hp' hfixed]
  rfl

end
end Universality.Rule

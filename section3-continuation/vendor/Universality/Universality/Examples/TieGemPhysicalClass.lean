import Universality.Percolation.CyclicPhysicalClass
import Universality.Examples.TieGemClassical

namespace Universality
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Rule
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

instance tieRule_interior_nonempty : Nonempty tieRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [tieRule.network.card_interior_vertices]
  have := tieRule_classical.vertices_gt_two
  omega

instance gemRule_interior_nonempty : Nonempty gemRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [gemRule.network.card_interior_vertices]
  have := gemRule_classical.vertices_gt_two
  omega

instance tieRule_edges_neZero : NeZero tieRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt tieRule_classical.edges_gt_one)⟩

instance gemRule_edges_neZero : NeZero gemRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt gemRule_classical.edges_gt_one)⟩

theorem tie_gem_same_physical_exponent_class (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    SameCriticalExponentUniversalityClass gemRule tieRule gemRule_classical.edges_gt_one
      tieRule_classical.edges_gt_one p (p ^ 2) := by
  have hsquare : p ^ 2 < 1 := by nlinarith [mul_pos hp (sub_pos.mpr hp')]
  apply gemRule_classical.same_exponent_class_of_equal_growth_data tieRule_classical p (p ^ 2)
    hp hp' hfixed (pow_pos hp 2) hsquare (tie_gem_fixed_point p hfixed).1
  · exact tie_gem_edges.2.trans tie_gem_edges.1.symm
  · exact tie_gem_distance.2.trans tie_gem_distance.1.symm
  · exact tie_gem_spectralRadius p hp hp' hfixed
  · exact tie_gem_response p hfixed

end
end Universality

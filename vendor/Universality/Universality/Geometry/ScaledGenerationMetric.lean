import Universality.Geometry.MetricDirectLimit
import Universality.Graph.CoarseDistance
import Universality.Graph.ClassicalSubstitution

/-! Actual finite generation metrics and their persistent old-vertex maps.
The distances are constructed from graph distances, rather than postulated
through a realised graph or a Hausdorff-dimension premise. -/

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

def scaledGenerationDistance (rule : Rule) (depth : ℕ)
    (first second : Fin (rule.generation depth).vertices) : ℝ :=
  ((rule.generation depth).network.fullGraph.dist first second : ℝ) /
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1)

theorem Classical.scale_real_pos {rule : Rule} (h : rule.Classical) :
    0 < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
  exact_mod_cast lt_trans Nat.zero_lt_one h.scale

abbrev scaledGenerationMetricSpace {rule : Rule} (h : rule.Classical) (depth : ℕ) :
    MetricSpace (Fin (rule.generation depth).vertices) where
  dist := scaledGenerationDistance rule depth
  dist_self vertex := by simp [scaledGenerationDistance]
  dist_comm first second := by simp [scaledGenerationDistance, SimpleGraph.dist_comm]
  dist_triangle first second third := by
    dsimp only [scaledGenerationDistance]
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right (pow_pos h.scale_real_pos _)).mpr
    exact_mod_cast (((h.generation depth).connected first).symm.trans
      ((h.generation depth).connected second)).dist_triangle_left third
  eq_of_dist_eq_zero := by
    intro first second hequal
    have hzero : ((rule.generation depth).network.fullGraph.dist first second : ℝ) = 0 :=
      (div_eq_zero_iff.mp hequal).resolve_right (ne_of_gt (pow_pos h.scale_real_pos _))
    have hzeroNat : (rule.generation depth).network.fullGraph.dist first second = 0 := by
      exact_mod_cast hzero
    exact ((((h.generation depth).connected first).symm.trans
      ((h.generation depth).connected second)).dist_eq_zero_iff).mp hzeroNat

def generationOldVertex (rule : Rule) (depth : ℕ) :
    Fin (rule.generation depth).vertices ↪ Fin (rule.generation (depth + 1)).vertices where
  toFun vertex := Fintype.equivFin
    ((rule.generation depth).network.SubstitutionVertex rule.network) (Sum.inl vertex)
  inj' := by
    intro first second hequal
    exact Sum.inl.inj ((Fintype.equivFin _).injective hequal)

theorem Classical.generationOldVertex_scaled_distance {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (first second : Fin (rule.generation depth).vertices) :
    scaledGenerationDistance rule (depth + 1)
        (rule.generationOldVertex depth first) (rule.generationOldVertex depth second) =
      scaledGenerationDistance rule depth first second := by
  have hcoarse := (rule.generation depth).network.substitute_coarse_distance rule.network
    first second (((h.generation depth).connected first).symm.trans
      ((h.generation depth).connected second)) (h.connected _)
  change (rule.generation (depth + 1)).network.fullGraph.dist
    (rule.generationOldVertex depth first) (rule.generationOldVertex depth second) = _ at hcoarse
  dsimp only [scaledGenerationDistance]
  rw [hcoarse, Nat.cast_mul, pow_succ]
  field_simp [ne_of_gt h.scale_real_pos]

theorem Classical.generationOldVertex_isometry {rule : Rule} (h : rule.Classical)
    (depth : ℕ) :
    letI := scaledGenerationMetricSpace h depth
    letI := scaledGenerationMetricSpace h (depth + 1)
    Isometry (rule.generationOldVertex depth) := by
  letI := scaledGenerationMetricSpace h depth
  letI := scaledGenerationMetricSpace h (depth + 1)
  apply Isometry.of_dist_eq
  exact h.generationOldVertex_scaled_distance depth

end
end Universality.Rule


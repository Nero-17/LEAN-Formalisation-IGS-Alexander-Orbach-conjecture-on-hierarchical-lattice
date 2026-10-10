import Universality.Percolation.PhysicalExponentClass
import Universality.Examples.ClassicalNoncommutativity

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Rule
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

instance groupedRule_interior_nonempty : Nonempty groupedRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [groupedRule.network.card_interior_vertices]
  have := groupedRule_classical.vertices_gt_two
  omega

instance alternatingRule_interior_nonempty : Nonempty alternatingRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [alternatingRule.network.card_interior_vertices]
  have := alternatingRule_classical.vertices_gt_two
  omega

instance groupedRule_edges_neZero : NeZero groupedRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt groupedRule_classical.edges_gt_one)⟩

instance alternatingRule_edges_neZero : NeZero alternatingRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt alternatingRule_classical.edges_gt_one)⟩

theorem reordered_physical_exponent_classes_differ :
    ¬ SameCriticalExponentUniversalityClass groupedRule alternatingRule
      groupedRule_classical.edges_gt_one alternatingRule_classical.edges_gt_one (1/2) (1/2) := by
  intro hequal
  have hdimensions := (groupedRule_classical.same_critical_exponent_class_iff_dimensions
    alternatingRule_classical (1/2) (1/2) (by norm_num) (by norm_num) reordered_rules_fixed_points.1
      (by norm_num) (by norm_num) reordered_rules_fixed_points.2).mp hequal
  have hmass := hdimensions.2.1
  rw [reordered_rules_terminal_distances.1, reordered_rules_terminal_distances.2] at hmass
  have hlog36 : Real.log (36 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogs := congrArg (fun x : ℝ => x * Real.log (36 : ℝ)) hmass
  simp only [Nat.cast_ofNat, div_mul_cancel₀ _ hlog36] at hlogs
  have hfirstPositive : 0 < (spectralRadius ℂ ((groupedRule.network.massMatrix (1/2)).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _)
      (groupedRule_classical.terminal_degree_spectral_bounds (1/2) (by norm_num) (by norm_num)).2.1
  have hsecondPositive : 0 < (spectralRadius ℂ ((alternatingRule.network.massMatrix (1/2)).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _)
      (alternatingRule_classical.terminal_degree_spectral_bounds (1/2) (by norm_num) (by norm_num)).2.1
  have hreal := Real.log_injOn_pos hfirstPositive hsecondPositive hlogs
  have hfirstFinite := (ENNReal.toReal_ne_zero.mp hfirstPositive.ne').2
  have hsecondFinite := (ENNReal.toReal_ne_zero.mp hsecondPositive.ne').2
  apply reordered_graph_mass_spectralRadii_ne
  have hh := congrArg ENNReal.ofReal hreal
  simpa only [ENNReal.ofReal_toReal hfirstFinite, ENNReal.ofReal_toReal hsecondFinite] using hh

theorem multiplicative_observations_fail_physical_classification
    {I T : Type*} [CommMonoid T] (observations : I → Rule → T)
    (hmul : ∀ i outer inner, outer.Classical → inner.Classical → (outer * inner).Classical →
      observations i (outer * inner) = observations i outer * observations i inner) :
    (fun i => observations i groupedRule) = (fun i => observations i alternatingRule) ∧
    ¬ SameCriticalExponentUniversalityClass groupedRule alternatingRule
      groupedRule_classical.edges_gt_one alternatingRule_classical.edges_gt_one (1/2) (1/2) :=
  ⟨reordered_classical_multiplicative_observations observations hmul,
    reordered_physical_exponent_classes_differ⟩

theorem multiplicative_dimensions_fail_physical_classification
    {I : Type*} (observations : I → Rule → ℝ)
    (hmul : ∀ i outer inner, outer.Classical → inner.Classical → (outer * inner).Classical →
      observations i (outer * inner) = observations i outer * observations i inner) :
    (fun i => Real.log (observations i groupedRule) /
      Real.log (groupedRule.network.fullGraph.dist groupedRule.network.source groupedRule.network.target)) =
    (fun i => Real.log (observations i alternatingRule) /
      Real.log (alternatingRule.network.fullGraph.dist alternatingRule.network.source alternatingRule.network.target)) ∧
    ¬ SameCriticalExponentUniversalityClass groupedRule alternatingRule
      groupedRule_classical.edges_gt_one alternatingRule_classical.edges_gt_one (1/2) (1/2) :=
  ⟨reordered_classical_multiplicative_dimensions observations hmul,
    reordered_physical_exponent_classes_differ⟩

theorem ambient_dimension_does_not_classify_physical_exponents :
    Real.log (groupedRule.edges : ℝ) /
      Real.log (groupedRule.network.fullGraph.dist groupedRule.network.source groupedRule.network.target : ℝ) =
    Real.log (alternatingRule.edges : ℝ) /
      Real.log (alternatingRule.network.fullGraph.dist alternatingRule.network.source alternatingRule.network.target : ℝ) ∧
    ¬ SameCriticalExponentUniversalityClass groupedRule alternatingRule
      groupedRule_classical.edges_gt_one alternatingRule_classical.edges_gt_one (1/2) (1/2) := by
  refine ⟨?_, reordered_physical_exponent_classes_differ⟩
  rw [reordered_rules_terminal_distances.1, reordered_rules_terminal_distances.2,
    reordered_rules_edge_counts.1, reordered_rules_edge_counts.2]

end
end Universality


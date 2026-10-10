import Universality.Examples.GraphThermalResponse
import Universality.Graph.TerminalSymmetricRule
import Universality.Percolation.ClusterMass

namespace Universality
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

theorem wheatstoneRule_terminalSymmetric : wheatstoneRule.TerminalSymmetric :=
  ⟨wheatstoneTerminalSymmetry, wheatstone_terminal_symmetry_source,
    wheatstone_terminal_symmetry_target⟩

theorem oppositeWheatstoneRule_terminalSymmetric : oppositeWheatstoneRule.TerminalSymmetric :=
  ⟨oppositeWheatstoneTerminalSymmetry, oppositeWheatstone_terminal_symmetry_source,
    oppositeWheatstone_terminal_symmetry_target⟩

theorem groupedRule_terminalSymmetric : groupedRule.TerminalSymmetric :=
  ((wheatstoneRule_terminalSymmetric.mul wheatstoneRule_terminalSymmetric).mul
    oppositeWheatstoneRule_terminalSymmetric).mul oppositeWheatstoneRule_terminalSymmetric

theorem alternatingRule_terminalSymmetric : alternatingRule.TerminalSymmetric :=
  ((wheatstoneRule_terminalSymmetric.mul oppositeWheatstoneRule_terminalSymmetric).mul
    wheatstoneRule_terminalSymmetric).mul oppositeWheatstoneRule_terminalSymmetric

theorem matrix_product_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : Matrix ι ι ℝ) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    ∀ i j, 0 < (A * B) i j := by
  intro i j
  exact Finset.sum_pos (fun k _ => mul_pos (hA i k) (hB k j)) Finset.univ_nonempty

theorem groupedFullMassMatrix_pos : ∀ σ τ, 0 < groupedFullMassMatrix σ τ :=
  matrix_product_pos _ _
    (matrix_product_pos _ _
      (matrix_product_pos _ _ wheatstoneMassMatrix_pos wheatstoneMassMatrix_pos)
      oppositeWheatstoneMassMatrix_pos) oppositeWheatstoneMassMatrix_pos

theorem alternatingFullMassMatrix_pos : ∀ σ τ, 0 < alternatingFullMassMatrix σ τ :=
  matrix_product_pos _ _
    (matrix_product_pos _ _
      (matrix_product_pos _ _ wheatstoneMassMatrix_pos oppositeWheatstoneMassMatrix_pos)
      wheatstoneMassMatrix_pos) oppositeWheatstoneMassMatrix_pos

def Rule.clusterMassGrowth (rule : Rule) (p : ℝ) (σ : LiveState) (n : ℕ) : ℝ :=
  Real.log ((rule.generation n).network.conditionalClusterMass p σ) /
    Real.log ((rule.generation n).network.fullGraph.dist
      (rule.generation n).network.source (rule.generation n).network.target)

theorem Rule.clusterMassGrowth_limit (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hp : 0 < p) (hp' : p < 1)
    (hsymmetric : rule.TerminalSymmetric)
    (reachable : rule.network.fullGraph.Reachable rule.network.source rule.network.target)
    (hplane : PreservesMassPlane (rule.network.massMatrix p))
    (hblock : ∀ i j, 0 < massPlaneBlock (rule.network.massMatrix p) i j)
    (hcolumn : ∀ σ, 0 < rule.network.massMatrix p σ .connected) (σ : LiveState) :
    Tendsto (rule.clusterMassGrowth p σ) atTop
      (𝓝 (Real.log (positiveRoot (massPlaneBlock (rule.network.massMatrix p))) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) := by
  obtain ⟨symmetry, hs, ht⟩ := hsymmetric
  apply rule.conditional_cluster_mass_dimension p hfixed hp hp' symmetry hs ht reachable
    (massPlaneLift ![massPlaneBlock (rule.network.massMatrix p) 0 1,
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
        massPlaneBlock (rule.network.massMatrix p) 0 0])
  · apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  · exact positiveRoot_pos _ hblock
  · rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul]
  · exact hcolumn

theorem groupedRule_clusterMassGrowth_limit (σ : LiveState) :
    Tendsto (groupedRule.clusterMassGrowth (1 / 2) σ) atTop
      (𝓝 (Real.log (positiveRoot groupedMassBlock) / Real.log 36)) := by
  have h := groupedRule.clusterMassGrowth_limit (1 / 2) reordered_rules_fixed_points.1
    (by norm_num) (by norm_num) groupedRule_terminalSymmetric
    ⟨groupedDistanceCertificate.walk⟩
    (by rw [groupedRule_mass]; exact groupedFullMassMatrix_preserves)
    (by rw [groupedRule_mass, groupedFullMassMatrix_block]; exact groupedMassBlock_pos)
    (by intro τ; rw [groupedRule_mass]; exact groupedFullMassMatrix_pos τ .connected) σ
  simpa only [groupedRule_mass, groupedFullMassMatrix_block,
    reordered_rules_terminal_distances.1, Nat.cast_ofNat] using h

theorem alternatingRule_clusterMassGrowth_limit (σ : LiveState) :
    Tendsto (alternatingRule.clusterMassGrowth (1 / 2) σ) atTop
      (𝓝 (Real.log (positiveRoot alternatingMassBlock) / Real.log 36)) := by
  have h := alternatingRule.clusterMassGrowth_limit (1 / 2) reordered_rules_fixed_points.2
    (by norm_num) (by norm_num) alternatingRule_terminalSymmetric
    ⟨alternatingDistanceCertificate.walk⟩
    (by rw [alternatingRule_mass]; exact alternatingFullMassMatrix_preserves)
    (by rw [alternatingRule_mass, alternatingFullMassMatrix_block]; exact alternatingMassBlock_pos)
    (by intro τ; rw [alternatingRule_mass]; exact alternatingFullMassMatrix_pos τ .connected) σ
  simpa only [alternatingRule_mass, alternatingFullMassMatrix_block,
    reordered_rules_terminal_distances.2, Nat.cast_ofNat] using h

/-- The different rates are limits of actual conditional open-cluster masses
on iterated finite graphs, not definitions assigned to a pair of matrices. -/
theorem reordered_graph_cluster_mass_dimensions_differ (σ : LiveState) :
    ∃ first second : ℝ, first ≠ second ∧
      Tendsto (groupedRule.clusterMassGrowth (1 / 2) σ) atTop (𝓝 first) ∧
      Tendsto (alternatingRule.clusterMassGrowth (1 / 2) σ) atTop (𝓝 second) := by
  refine ⟨Real.log (positiveRoot groupedMassBlock) / Real.log 36,
    Real.log (positiveRoot alternatingMassBlock) / Real.log 36, ?_,
    groupedRule_clusterMassGrowth_limit σ, alternatingRule_clusterMassGrowth_limit σ⟩
  simpa only [logarithmicSpectralGrowth,
    spectralRadius_positive_twoByTwo _ groupedMassBlock_pos,
    spectralRadius_positive_twoByTwo _ alternatingMassBlock_pos,
    ENNReal.toReal_ofReal (positiveRoot_pos _ groupedMassBlock_pos).le,
    ENNReal.toReal_ofReal (positiveRoot_pos _ alternatingMassBlock_pos).le] using
    noncommutative_logarithmic_growth_ne

theorem no_multiplicative_classification_of_cluster_mass_growth {I T : Type*} [CommMonoid T]
    (observations : I → Rule → T)
    (hmul : ∀ i outer inner, observations i (outer * inner) =
      observations i outer * observations i inner) :
    ¬ ∃ classify : (I → T) → ℝ, ∀ rule : Rule,
      rule.TerminalSymmetric → rule.network.reliability (1 / 2) = 1 / 2 →
      Tendsto (rule.clusterMassGrowth (1 / 2) .connected) atTop
        (𝓝 (classify (fun i => observations i rule))) := by
  rintro ⟨classify, hclassify⟩
  obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
    reordered_graph_cluster_mass_dimensions_differ .connected
  have hg := tendsto_nhds_unique hfirst
    (hclassify groupedRule groupedRule_terminalSymmetric reordered_rules_fixed_points.1)
  have ha := tendsto_nhds_unique hsecond
    (hclassify alternatingRule alternatingRule_terminalSymmetric reordered_rules_fixed_points.2)
  apply hne
  rw [hg, ha, reordered_graph_multiplicative_observations observations hmul]

end
end Universality

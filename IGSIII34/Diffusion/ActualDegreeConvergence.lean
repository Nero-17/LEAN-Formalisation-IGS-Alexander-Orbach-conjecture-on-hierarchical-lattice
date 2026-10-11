import IGSIII34.Diffusion.ActualMeasureComparison
import IGSIII34.Diffusion.VanishingComparison
import IGSIII.Geometry.ActualCriticalMesh
import IGSIII.Mass.HistoryPathLaw

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem actual_degree_counting_tendsto_zero_of_component_radius_bounds
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale)
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened fine, start ≤ address.length →
      (markedTerminalComponentRadius rule marks fine address opened : ℝ) / scale ^ (fine + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (massGrowth : Tendsto (fun depth => markedComponentVertexMass rule marks depth []) atTop atTop)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (limits : ∀ age (fallback word : Fin age → (Fin rule.edges × Bool)),
      Tendsto (fun fine => edgeComponentWordWeight rule marks fine age word) atTop (𝓝 (weight (List.ofFn word))) ∧
      Tendsto (fun fine => fullComponentEmpiricalWordWeight rule marks fine age fallback word) atTop (𝓝 (weight (List.ofFn word)))) :
    Tendsto (fun depth => levyProkhorovEDist
      (actualFiniteClusterDegreeMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive depth)
      (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        scale scalePositive depth)) atTop (𝓝 0) := by
  classical
  obtain ⟨edge⟩ := clusterEdge_nonempty rule.network (marks ([], true)) (crossing [] true)
  let fallback : ∀ age, Fin age → (Fin rule.edges × Bool) := fun _ _ => (edge.val, true)
  let error := fun age fine =>
    (∑ word : Fin (age + 1) → (Fin rule.edges × Bool), ENNReal.ofReal
      |edgeComponentWordWeight rule marks fine (age + 1) word -
        fullComponentEmpiricalWordWeight rule marks fine (age + 1) (fallback (age + 1)) word|) +
      actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        scale scalePositive (fine + (age + 1))
        (actualComponentVertexFrontier rule marks crossing scale scalePositive fine (age + 1))
  have meshConvergence : Tendsto (fun age : ℕ => ENNReal.ofReal (coefficient * eta ^ (age + 1))) atTop (𝓝 0) := by
    have realConvergence : Tendsto (fun age : ℕ => coefficient * eta ^ (age + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
        ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp realConvergence
  have errorConvergence : ∀ age, Tendsto (error age) atTop (𝓝 0) := by
    intro age
    have realConvergence : Tendsto (fun fine => ∑ word : Fin (age + 1) → (Fin rule.edges × Bool),
        |edgeComponentWordWeight rule marks fine (age + 1) word -
          fullComponentEmpiricalWordWeight rule marks fine (age + 1) (fallback (age + 1)) word|) atTop (𝓝 0) := by
      have result := tendsto_finsetSum Finset.univ (fun (word : Fin (age + 1) → (Fin rule.edges × Bool)) _ =>
        ((limits (age + 1) (fallback (age + 1)) word).1.sub (limits (age + 1) (fallback (age + 1)) word).2).abs)
      simpa only [sub_self, abs_zero, Finset.sum_const_zero] using result
    have ennrealConvergence : Tendsto (fun fine => ∑ word : Fin (age + 1) → (Fin rule.edges × Bool), ENNReal.ofReal
        |edgeComponentWordWeight rule marks fine (age + 1) word -
          fullComponentEmpiricalWordWeight rule marks fine (age + 1) (fallback (age + 1)) word|) atTop (𝓝 0) := by
      simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun word _ => abs_nonneg (_ - _))]
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp realConvergence
    have result := ennrealConvergence.add
      (actual_component_vertex_frontier_mass_tendsto_zero rule marks crossing scale scalePositive massGrowth (age + 1))
    simpa only [error, add_zero] using result
  apply tendsto_zero_of_shifted_comparison _ _ error start meshConvergence errorConvergence
  intro age beyond fine
  have bound := actual_degree_counting_comparison_bound rule marks crossing coherent scale scalePositive fine age
    (fallback (age + 1)) (coefficient * eta ^ (age + 1)) (mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _))
    (fun word => by
      have result := radiusBound (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened fine
        (by simpa only [componentEdgeAddress, List.length_map, List.length_ofFn] using beyond)
      simpa only [componentEdgeAddress, List.length_map, List.length_ofFn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result)
  exact bound.trans_eq (by dsimp only [error]; ac_rfl)

/-- Degree and full counting probability measures on the same actual finite
critical clusters are asymptotically indistinguishable. All component reward,
frontier, coherence and mesh inputs are discharged by existing proved results. -/
theorem exists_actual_critical_degree_counting_measure_comparison
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ scale : ℝ, ∃ scalePositive : 0 < scale,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ scale ∧
      scale ≤ longestTerminalPath rule.network ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∃ crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened,
          Tendsto (fun depth => levyProkhorovEDist
            (actualFiniteClusterDegreeMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive depth)
            (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              scale scalePositive depth)) atTop (𝓝 0) := by
  obtain ⟨scale, scaleLower, scaleUpper, meshes⟩ := exists_actual_critical_uniform_component_mesh rule classicalRule
    p positive belowOne fixedPoint
  have scaleGreaterThanOne : 1 < scale :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le scaleLower
  have scalePositive : 0 < scale := zero_lt_one.trans scaleGreaterThanOne
  let eta : ℝ := (scale + 1) / (2 * scale)
  have etaPositive : 0 < eta := div_pos (by linarith) (by positivity)
  have etaBelowOne : eta < 1 := (div_lt_one (by positivity : 0 < 2 * scale)).mpr (by linarith)
  have productGreaterThanOne : 1 < scale * eta := by
    have identity : scale * eta = (scale + 1) / 2 := by dsimp [eta]; field_simp
    rw [identity]
    linarith
  obtain ⟨weight, weightLimits⟩ := actual_joint_edge_counting_word_limits classicalRule p positive belowOne fixedPoint
  refine ⟨scale, scalePositive, scaleLower, scaleUpper, ?_⟩
  filter_upwards [weightLimits, meshes eta etaPositive etaBelowOne productGreaterThanOne,
    actual_component_root_mass_tendsto_atTop classicalRule p positive belowOne fixedPoint,
    marked_generations_coherent_ae rule p positive belowOne fixedPoint]
    with marks weightLimits mesh growth coherent
  obtain ⟨start, radiusBound⟩ := mesh
  refine ⟨weightLimits.1, ?_⟩
  exact actual_degree_counting_tendsto_zero_of_component_radius_bounds rule marks weightLimits.1 (coherent [] true) scale scalePositive
    eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le) radiusBound growth
    (fun address => weight address marks) weightLimits.2.2.2

end
end IGSIII34.Diffusion

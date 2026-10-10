import IGSIII.Mass.CylinderCounts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- All five mask limits on their original conditioned path laws. The B
limit and its two one-arm limits are functions of the same raw history. -/
theorem Classical.oriented_mask_vertex_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ limit : OrientedState → (Π n, rule.ConfigurationHistory n) → ℝ,
      (∀ path, limit .inactive path = 0) ∧
      (∀ path, limit .both path = limit .sourceOnly path + limit .targetOnly path) ∧
      ∀ parent,
      ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point parent.massOpened,
        0 ≤ limit parent path ∧
        Tendsto (fun n => ((rule.generation n).network.internalStateMass parent
          (ConfigurationHistory.latest rule n (path n)) : ℝ) /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (limit parent path)) ∧
        (parent = .connected → 0 < limit parent path) := by
  obtain ⟨connected, _, connected_convergence, connected_positive, _⟩ :=
    classicalRule.internal_connected_vertex_mass_ae_L2_positive p positive below_one fixed_point
  obtain ⟨both, source, target, _, _, _, joint_split, joint_convergence⟩ :=
    classicalRule.joint_both_mask_vertex_limits p positive below_one fixed_point
  refine ⟨(fun parent path => match parent with
    | .connected => connected path
    | .both => both path
    | .sourceOnly => source path
    | .targetOnly => target path
    | .inactive => 0), fun _ => rfl, joint_split, ?_⟩
  intro parent
  cases parent with
  | connected =>
    filter_upwards [connected_convergence, connected_positive,
      ConfigurationHistory.infiniteLaw_crosses rule p positive below_one fixed_point true] with path convergence strictly_positive crossing
    refine ⟨strictly_positive.le, ?_, fun _ => strictly_positive⟩
    convert convergence using 1
    ext n
    simp only [internalStateMass, OrientedState.sourceSelected, OrientedState.targetSelected,
      ConfigurationHistory.vertexMass, show (LiveState.connected == LiveState.both) = false from rfl]
    rw [(rule.generation n).network.internalSelectedMass_connected _ (crossing n)]
  | both =>
    filter_upwards [joint_convergence] with path convergence
    exact ⟨convergence.1, convergence.2.2.2.2.1, fun impossible => OrientedState.noConfusion impossible⟩
  | sourceOnly =>
    filter_upwards [joint_convergence] with path convergence
    exact ⟨convergence.2.1, convergence.2.2.2.2.2.1, fun impossible => OrientedState.noConfusion impossible⟩
  | targetOnly =>
    filter_upwards [joint_convergence] with path convergence
    exact ⟨convergence.2.2.1, convergence.2.2.2.2.2.2, fun impossible => OrientedState.noConfusion impossible⟩
  | inactive =>
    apply Filter.Eventually.of_forall
    intro path
    refine ⟨le_rfl, ?_, fun impossible => OrientedState.noConfusion impossible⟩
    simpa only [internalStateMass_inactive, Nat.cast_zero, zero_div] using tendsto_const_nhds

end Universality.Rule

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- Simultaneous actual mass limits at all addresses and masks on the common
independent mark space, retaining the original joint B coupling. -/
theorem marked_oriented_vertex_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∃ limit : List (Fin rule.edges) → OrientedState →
        (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ address marks, limit address .inactive marks = 0) ∧
      (∀ address marks, limit address .both marks =
        limit address .sourceOnly marks + limit address .targetOnly marks) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
        ∀ address parent,
          0 ≤ limit address parent marks ∧
          Tendsto (fun n => markedOrientedVertexMass rule marks n address parent /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
            atTop (𝓝 (limit address parent marks)) ∧
          (parent = .connected → 0 < limit address parent marks) := by
  obtain ⟨root_limit, inactive, joint_split, convergence⟩ := classicalRule.oriented_mask_vertex_limits
    p positive below_one fixed_point
  refine ⟨fun address parent marks => root_limit parent
    (markedHistoryPath rule address parent.massOpened marks), ?_, ?_, ?_⟩
  · intro address marks
    exact inactive _
  · intro address marks
    exact joint_split _
  apply ae_all_iff.mpr
  intro address
  apply ae_all_iff.mpr
  intro parent
  have marginal_convergence := convergence parent
  rw [← independentInnovationLaw_history_path rule p positive below_one fixed_point address parent.massOpened]
    at marginal_convergence
  have pulled := ae_of_ae_map (markedHistoryPath_measurable rule address parent.massOpened).aemeasurable
    marginal_convergence
  filter_upwards [pulled] with marks convergence
  simpa only [markedOrientedVertexMass, markedHistoryPath, Rule.ConfigurationHistory.latest_ofFine] using convergence

end IGSIII.Chemical.Substitution

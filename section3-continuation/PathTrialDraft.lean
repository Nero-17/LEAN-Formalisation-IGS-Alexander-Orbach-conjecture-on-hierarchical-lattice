import IGSIII34.Resistance.DistanceEnergy

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem exists_signed_edge_flow_of_adjacent (network : FiniteNetwork Vertex Edge)
    {first second : Vertex} (adjacent : network.graph.Adj first second) :
    ∃ (edge : Edge) (sign : ℝ), sign ^ 2 = 1 ∧
      network.flowBetween first second (fun index => if index = edge then sign else 0) ∧
      (network.endpoint edge = (first, second) ∨ network.endpoint edge = (second, first)) := by
  obtain ⟨_, edge, orientation⟩ := adjacent
  rcases orientation with forward | backward
  · refine ⟨edge, 1, by norm_num, ?_, Or.inl forward⟩
    intro vertex
    rw [network.divergence_single, forward]
  · refine ⟨edge, -1, by norm_num, ?_, Or.inr backward⟩
    intro vertex
    simp [divergence, backward, eq_comm]

theorem energy_add_single_of_zero (resistance current : Edge → ℝ) (edge : Edge)
    (sign : ℝ) (zeroCurrent : current edge = 0) :
    energy resistance (fun index => (if index = edge then sign else 0) + current index) =
      resistance edge * sign ^ 2 + energy resistance current := by
  have pointwise (index : Edge) :
      resistance index * ((if index = edge then sign else 0) + current index) ^ 2 =
        (if index = edge then resistance index * sign ^ 2 else 0) +
          resistance index * current index ^ 2 := by
    by_cases same : index = edge
    · subst index
      simp [zeroCurrent]
    · simp [same]
  simp only [energy, pointwise, Finset.sum_add_distrib]
  simp

theorem exists_unit_energy_path_flow (network : FiniteNetwork Vertex Edge)
    {first second : Vertex} (walk : network.graph.Walk first second) (path : walk.IsPath) :
    ∃ current : Edge → ℝ, network.flowBetween first second current ∧
      (∀ edge, current edge ≠ 0 →
        (network.endpoint edge).1 ∈ walk.support ∧ (network.endpoint edge).2 ∈ walk.support) ∧
      energy (fun _ => 1) current = (walk.length : ℝ) := by
  revert path
  induction walk with
  | nil =>
      intro _
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro vertex
        simp [divergence]
      · intro edge nonzero
        exact False.elim (nonzero rfl)
      · simp [energy]
  | @cons first middle last adjacent walk inductionHypothesis =>
      intro path
      have pathProperties := (SimpleGraph.Walk.cons_isPath_iff adjacent walk).mp path
      obtain ⟨tailCurrent, tailFlow, tailSupport, tailEnergy⟩ := inductionHypothesis pathProperties.1
      obtain ⟨edge, sign, signSquare, edgeFlow, orientation⟩ :=
        network.exists_signed_edge_flow_of_adjacent adjacent
      have firstEndpoint : (network.endpoint edge).1 = first ∨ (network.endpoint edge).2 = first := by
        rcases orientation with forward | backward
        · exact Or.inl (congrArg Prod.fst forward)
        · exact Or.inr (congrArg Prod.snd backward)
      have zeroTail : tailCurrent edge = 0 := by
        by_contra nonzero
        have endpoints := tailSupport edge nonzero
        rcases firstEndpoint with firstEquals | secondEquals
        · exact pathProperties.2 (firstEquals ▸ endpoints.1)
        · exact pathProperties.2 (secondEquals ▸ endpoints.2)
      refine ⟨fun index => (if index = edge then sign else 0) + tailCurrent index,
        network.flowBetween_add edgeFlow tailFlow, ?_, ?_⟩
      · intro index nonzero
        by_cases same : index = edge
        · subst index
          rcases orientation with forward | backward
          · simp [forward, SimpleGraph.Walk.support_cons, walk.start_mem_support]
          · simp [backward, SimpleGraph.Walk.support_cons, walk.start_mem_support]
        · have tailNonzero : tailCurrent index ≠ 0 := by simpa [same] using nonzero
          obtain ⟨firstInside, secondInside⟩ := tailSupport index tailNonzero
          exact ⟨List.mem_cons_of_mem _ firstInside, List.mem_cons_of_mem _ secondInside⟩
      · rw [energy_add_single_of_zero _ _ _ _ zeroTail, signSquare, tailEnergy]
        simp only [one_mul, SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem unitResistance_le_distance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    network.effectiveResistance (fun _ => 1) ≤ (network.graph.dist network.source network.target : ℝ) := by
  obtain ⟨walk, shortest⟩ := connected.exists_walk_length_eq_dist
  obtain ⟨current, unitFlow, _, energyIdentity⟩ :=
    network.exists_unit_energy_path_flow walk (walk.isPath_of_length_eq_dist shortest)
  exact (network.effectiveResistance_le_energy (fun _ => zero_le_one) unitFlow).trans_eq
    (energyIdentity.trans (by rw [shortest]))

end
end IGSIII34.Resistance.FiniteNetwork

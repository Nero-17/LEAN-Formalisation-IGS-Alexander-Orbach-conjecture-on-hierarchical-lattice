import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The chemical recursion on genuinely independent connected innovations

The connected marks are independent with the actual conditioned rule law.
The local completion changes them only on a null event and preserves both
their law and independence. Noncrossing marks remain in the actual full
generation configuration, and the shortest-path proof excludes them only
when the corresponding coarse edge is absent from the selected path.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory

theorem exists_conditioned_crossing_configuration (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ configuration : Configuration rule.edges, rule.network.crosses configuration = true := by
  letI := Rule.ConfigurationHistory.law_probability rule p positive lessOne fixedPoint true 0
  have crossing := history_law_latest_crosses rule p positive lessOne fixedPoint true 0
  exact crossing.exists

noncomputable def conditionedCrossingConfiguration (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) : Configuration rule.edges :=
  (exists_conditioned_crossing_configuration rule p positive lessOne fixedPoint).choose

theorem conditionedCrossingConfiguration_crosses (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    rule.network.crosses (conditionedCrossingConfiguration rule p positive lessOne fixedPoint) = true :=
  (exists_conditioned_crossing_configuration rule p positive lessOne fixedPoint).choose_spec

noncomputable def independentCrossingConfiguration (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) : Configuration rule.edges :=
  if rule.network.crosses (marks (address, true)) then marks (address, true)
  else conditionedCrossingConfiguration rule p positive lessOne fixedPoint

theorem independentCrossingConfiguration_crosses (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) :
    rule.network.crosses (independentCrossingConfiguration rule p positive lessOne fixedPoint marks address) = true := by
  unfold independentCrossingConfiguration
  split
  · assumption
  · exact conditionedCrossingConfiguration_crosses rule p positive lessOne fixedPoint

theorem independentCrossingConfiguration_eq_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∀ address, independentCrossingConfiguration rule p positive lessOne fixedPoint marks address =
        marks (address, true) := by
  filter_upwards [independentInnovationLaw_crosses rule p positive lessOne fixedPoint] with marks crossing
  intro address
  simp only [independentCrossingConfiguration, crossing address true, if_true]

theorem independentCrossingConfiguration_law (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => independentCrossingConfiguration rule p positive lessOne fixedPoint marks address) =
      Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint true 0 := by
  have same := independentCrossingConfiguration_eq_ae rule p positive lessOne fixedPoint
  exact (Measure.map_congr (same.mono (fun marks equality => equality address))).trans
    (independentInnovationLaw_marginal rule p positive lessOne fixedPoint address true)

theorem independentCrossingConfiguration_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    iIndepFun (fun address marks => independentCrossingConfiguration rule p positive lessOne fixedPoint marks address)
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
  have crossingMarks : iIndepFun (fun address marks => marks (address, true))
      (independentInnovationLaw rule p positive lessOne fixedPoint) :=
    (independentInnovationLaw_independent rule p positive lessOne fixedPoint).precomp
      (fun first second equality => congrArg Prod.fst equality)
  exact crossingMarks.comp
    (fun _ configuration => if rule.network.crosses configuration then configuration
      else conditionedCrossingConfiguration rule p positive lessOne fixedPoint)
    (fun _ => measurable_of_countable _)

noncomputable def bondEdgeIndex (rule : Rule) (bond : Sym2 (Fin rule.vertices)) : Option (Fin rule.edges) := by
  classical
  exact if represented : ∃ edge, s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) = bond
    then some represented.choose else none

theorem bondEdgeIndex_endpoint (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2))) (edge : Fin rule.edges) :
    bondEdgeIndex rule s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) = some edge := by
  classical
  have represented : ∃ child, s((rule.network.endpoint child).1, (rule.network.endpoint child).2) =
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) := ⟨edge, rfl⟩
  simp only [bondEdgeIndex, dif_pos represented]
  rw [simple represented.choose_spec]

noncomputable def bondAddressIndices (rule : Rule) (address : List (Sym2 (Fin rule.vertices))) :
    List (Fin rule.edges) := address.filterMap (bondEdgeIndex rule)

theorem bondAddressIndices_endpoint (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (address : List (Sym2 (Fin rule.vertices))) (edge : Fin rule.edges) :
    bondAddressIndices rule
        (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]) =
      bondAddressIndices rule address ++ [edge] := by
  simp only [bondAddressIndices, List.filterMap_append, List.filterMap_cons,
    bondEdgeIndex_endpoint rule simple, List.filterMap_nil]

noncomputable def independentChemicalInnovation (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (rootAddress : List (Fin rule.edges)) (address : List (Sym2 (Fin rule.vertices))) :
    Configuration rule.edges :=
  independentCrossingConfiguration rule p positive lessOne fixedPoint marks
    (rootAddress ++ bondAddressIndices rule address)

theorem independentChemicalInnovation_crosses (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (rootAddress : List (Fin rule.edges)) (address : List (Sym2 (Fin rule.vertices))) :
    rule.network.crosses (independentChemicalInnovation rule p positive lessOne fixedPoint marks rootAddress address) =
      true := independentCrossingConfiguration_crosses rule p positive lessOne fixedPoint marks _

noncomputable def independentChemicalDistance (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (rootAddress : List (Fin rule.edges)) (depth : ℕ) : ℝ :=
  terminalDistance (innovationPathFamily rule
    (independentChemicalInnovation rule p positive lessOne fixedPoint marks rootAddress)
    (independentChemicalInnovation_crosses rule p positive lessOne fixedPoint marks rootAddress)) [] depth

theorem marked_distance_eq_independent_terminalDistance (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (rootAddress : List (Fin rule.edges)) (depth : ℕ)
    (address : List (Sym2 (Fin rule.vertices))) :
    (((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth
        (rootAddress ++ bondAddressIndices rule address) true)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) =
      terminalDistance (innovationPathFamily rule
        (independentChemicalInnovation rule p positive lessOne fixedPoint marks rootAddress)
        (independentChemicalInnovation_crosses rule p positive lessOne fixedPoint marks rootAddress))
          address (depth + 1) := by
  have innovation (address : List (Sym2 (Fin rule.vertices))) :
      independentChemicalInnovation rule p positive lessOne fixedPoint marks rootAddress address =
        marks (rootAddress ++ bondAddressIndices rule address, true) := by
    simp only [independentChemicalInnovation, independentCrossingConfiguration, crossing _ true, if_true]
  induction depth generalizing address with
  | zero =>
      rw [terminalDistance_succ]
      simp only [terminalDistance_zero, innovationPathFamily, innovation, markedGenerationConfiguration]
      exact (graphPathFamily_shortest_unit _ _ _ ((rule.network.crosses_eq_true _).mp (crossing _ true))).symm
  | succ depth inductionHypothesis =>
      have reachable : (rule.network.openGraph
          (marks (rootAddress ++ bondAddressIndices rule address, true))).Reachable
          rule.network.source rule.network.target := (rule.network.crosses_eq_true _).mp (crossing _ true)
      rw [generation_distance_eq_cellMinPlus rule simple, markedGenerationConfiguration_root rule marks crossing,
        cellMinPlus, weightedDistance_of_reachable _ _ reachable, terminalDistance_succ]
      simp only [innovationPathFamily, innovation]
      apply shortest_congr_used
      intro path membership bond edgeMembership
      obtain ⟨edge, retained, rfl⟩ := graphPathFamily_used_edge rule.network _ reachable membership edgeMembership
      rw [childDistanceCost_endpoint rule.network (rule.generation depth).network _ simple edge,
        markedGenerationConfiguration_topCells]
      simp only [retained]
      simpa only [bondAddressIndices_endpoint rule simple, List.append_assoc] using
        inductionHypothesis (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)])

theorem independent_chemical_distance_eq_actual_ae (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∀ address depth,
        independentChemicalDistance rule p positive lessOne fixedPoint marks address (depth + 1) =
          (((rule.generation depth).network.openGraph
            (markedGenerationConfiguration rule marks depth address true)).dist
              (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) := by
  filter_upwards [independentInnovationLaw_crosses rule p positive lessOne fixedPoint] with marks crossing
  intro address depth
  simpa only [independentChemicalDistance, bondAddressIndices, List.filterMap_nil, List.append_nil] using
    (marked_distance_eq_independent_terminalDistance rule simple p positive lessOne fixedPoint
      marks crossing address depth []).symm

theorem independent_chemical_distance_law (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) (depth : ℕ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => independentChemicalDistance rule p positive lessOne fixedPoint marks address (depth + 1)) =
      (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint true depth).map
        (fun history => (((rule.generation depth).network.openGraph
          (Rule.ConfigurationHistory.latest rule depth history)).dist
            (rule.generation depth).network.source (rule.generation depth).network.target : ℝ)) := by
  have same := independent_chemical_distance_eq_actual_ae rule simple p positive lessOne fixedPoint
  rw [Measure.map_congr (same.mono (fun marks equality => equality address depth))]
  have markedHistoryMeasurable : Measurable (fun marks => Rule.ConfigurationHistory.ofFine rule depth
      (markedGenerationConfiguration rule marks depth address true)) := by
    simpa only [Function.comp_def] using
      (measurable_of_countable (Rule.ConfigurationHistory.ofFine rule depth)).comp
        (markedGenerationConfiguration_measurable rule depth address true)
  rw [← independentInnovationLaw_history_marginal rule p positive lessOne fixedPoint depth address true,
    Measure.map_map (measurable_of_countable _) markedHistoryMeasurable]
  congr 1
  funext marks
  rw [Function.comp_apply, Rule.ConfigurationHistory.latest_ofFine]

end IGSIII.Chemical.Substitution

import IGSIII.Mass.FourStateMassPerron
import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders
import Mathlib.MeasureTheory.Constructions.Projective

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule.ConfigurationHistory

open FiniteNetwork MeasureTheory

/-- Recover an earlier complete history from a later complete history. -/
noncomputable def truncate (rule : Rule) : (depth : ℕ) → rule.ConfigurationHistory depth →
    (earlier : ℕ) → earlier ≤ depth → rule.ConfigurationHistory earlier
  | 0, history, earlier, bound => by
      have equality : earlier = 0 := by omega
      subst earlier
      exact history
  | depth + 1, history, earlier, bound =>
      if equality : earlier = depth + 1 then equality.symm ▸ history
      else truncate rule depth history.1 earlier (by omega)

theorem truncate_of_extends (rule : Rule) (path : Π n, rule.ConfigurationHistory n)
    (extension_identity : ∀ n, (path (n + 1)).1 = path n) (depth earlier : ℕ) (bound : earlier ≤ depth) :
    truncate rule depth (path depth) earlier bound = path earlier := by
  induction depth with
  | zero =>
    have equality : earlier = 0 := by omega
    subst earlier
    rfl
  | succ depth induction_hypothesis =>
    by_cases equality : earlier = depth + 1
    · subst earlier
      simp [truncate]
    · simp only [truncate, dif_neg equality]
      rw [extension_identity depth]
      exact induction_hypothesis (by omega)

/-- Since each history already stores the whole past, its one-time marginals
and almost-sure extension identities determine the complete infinite law. -/
theorem eq_of_extends_and_marginals (rule : Rule)
    (first second : Measure (Π n, rule.ConfigurationHistory n))
    [IsFiniteMeasure first] [IsFiniteMeasure second]
    (first_extends : ∀ᵐ path ∂first, ∀ n, (path (n + 1)).1 = path n)
    (second_extends : ∀ᵐ path ∂second, ∀ n, (path (n + 1)).1 = path n)
    (marginals : ∀ n, first.map (fun path => path n) = second.map (fun path => path n)) :
    first = second := by
  classical
  apply IsProjectiveLimit.unique (P := fun indices : Finset ℕ => second.map indices.restrict) ?_ (fun _ => rfl)
  intro indices
  change first.map indices.restrict = second.map indices.restrict
  have index_bound (index : indices) : index.val ≤ indices.sup id := by
    exact Finset.le_sup (f := id) index.property
  have first_prefix : indices.restrict =ᵐ[first]
      fun path index => truncate rule (indices.sup id) (path (indices.sup id)) index.val
        (index_bound index) := by
    filter_upwards [first_extends] with path extension_identity
    funext index
    exact (truncate_of_extends rule path extension_identity _ _ _).symm
  have second_prefix : indices.restrict =ᵐ[second]
      fun path index => truncate rule (indices.sup id) (path (indices.sup id)) index.val
        (index_bound index) := by
    filter_upwards [second_extends] with path extension_identity
    funext index
    exact (truncate_of_extends rule path extension_identity _ _ _).symm
  rw [Measure.map_congr first_prefix, Measure.map_congr second_prefix]
  have prefix_measurable : Measurable (fun history : rule.ConfigurationHistory (indices.sup id) =>
      fun index : indices => truncate rule (indices.sup id) history index.val
        (index_bound index)) := measurable_of_countable _
  change first.map ((fun history : rule.ConfigurationHistory (indices.sup id) =>
      fun index : indices => truncate rule (indices.sup id) history index.val (index_bound index)) ∘
        fun path => path (indices.sup id)) =
    second.map ((fun history : rule.ConfigurationHistory (indices.sup id) =>
      fun index : indices => truncate rule (indices.sup id) history index.val (index_bound index)) ∘
        fun path => path (indices.sup id))
  rw [← Measure.map_map prefix_measurable (measurable_pi_apply _),
    ← Measure.map_map prefix_measurable (measurable_pi_apply _), marginals]

end Universality.Rule.ConfigurationHistory

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory

/-- The complete actual history at an address in the common mark space. -/
noncomputable def markedHistoryPath (rule : Rule)
    (address : List (Fin rule.edges)) (opened : Bool)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    Π depth, rule.ConfigurationHistory depth :=
  fun depth => Rule.ConfigurationHistory.ofFine rule depth
    (markedGenerationConfiguration rule marks depth address opened)

theorem markedHistoryPath_measurable (rule : Rule) (address : List (Fin rule.edges)) (opened : Bool) :
    Measurable (markedHistoryPath rule address opened) := by
  apply measurable_pi_lambda
  intro depth
  exact (measurable_of_countable (Rule.ConfigurationHistory.ofFine rule depth)).comp
    (markedGenerationConfiguration_measurable rule depth address opened)

theorem markedHistoryPath_extends (rule : Rule) (p : ℝ) (positive : 0 < p)
    (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
      ∀ address opened depth,
        (markedHistoryPath rule address opened marks (depth + 1)).1 =
          markedHistoryPath rule address opened marks depth := by
  filter_upwards [marked_generations_coherent_ae rule p positive below_one fixed_point] with marks coherent
  intro address opened depth
  change Rule.ConfigurationHistory.ofFine rule depth
      (rule.coarsenGeneration depth (markedGenerationConfiguration rule marks (depth + 1) address opened)) = _
  rw [coherent address opened depth]
  rfl

/-- Finite-cylinder identification promotes to equality of the complete path
law; hence all previously proved almost-sure mass limits transfer to every address. -/
theorem independentInnovationLaw_history_path (rule : Rule) (p : ℝ) (positive : 0 < p)
    (below_one : p < 1) (fixed_point : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (opened : Bool) :
    (independentInnovationLaw rule p positive below_one fixed_point).map
      (markedHistoryPath rule address opened) =
        Rule.ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point opened := by
  letI : IsProbabilityMeasure ((independentInnovationLaw rule p positive below_one fixed_point).map
      (markedHistoryPath rule address opened)) :=
    Measure.isProbabilityMeasure_map (markedHistoryPath_measurable rule address opened).aemeasurable
  apply Rule.ConfigurationHistory.eq_of_extends_and_marginals rule
  · apply (ae_map_iff (markedHistoryPath_measurable rule address opened).aemeasurable
      (by
        simp only [Set.setOf_forall]
        apply MeasurableSet.iInter
        intro depth
        exact measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply (depth + 1)))
          (measurable_pi_apply depth))).mpr
    filter_upwards [markedHistoryPath_extends rule p positive below_one fixed_point] with marks extension_identity
    exact extension_identity address opened
  · exact Rule.ConfigurationHistory.infiniteLaw_extends rule p positive below_one fixed_point opened
  · intro depth
    rw [Measure.map_map (measurable_pi_apply depth) (markedHistoryPath_measurable rule address opened),
      Rule.ConfigurationHistory.infiniteLaw_marginal]
    exact independentInnovationLaw_history_marginal rule p positive below_one fixed_point depth address opened

end IGSIII.Chemical.Substitution

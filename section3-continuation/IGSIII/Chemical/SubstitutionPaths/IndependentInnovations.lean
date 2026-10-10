import IGSIII.Chemical.SubstitutionPaths.ChildHistoryLaw
import IGSIII.Chemical.SubstitutionPaths.ConnectedTree
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Independent crossing and noncrossing configuration innovations

The coordinate law at `(address, opened)` is the existing depth-zero IGS II
conditioned configuration law. All such coordinates are independent on the
actual countable product probability space. A parent selects the coordinate
matching its crossing state. The same noncrossing coordinate is available to
both one-terminal masks, so the construction does not resample a B-cell.

The full finite generation below retains every selected noncrossing cell.
Its crossing and coarsening identities are proved from the actual graph
reassociation. Identification of its finite probability laws is separate.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory

noncomputable def independentInnovationLaw (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    Measure ((List (Fin rule.edges) × Bool) → Configuration rule.edges) :=
  Measure.infinitePi (fun coordinate : List (Fin rule.edges) × Bool =>
    Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0)

instance independentInnovationLaw_probability (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    IsProbabilityMeasure (independentInnovationLaw rule p positive lessOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive lessOne fixedPoint coordinate.2 0
  unfold independentInnovationLaw
  infer_instance

theorem independentInnovationLaw_marginal (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (opened : Bool) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).map
        (fun marks => marks (address, opened)) =
      Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint opened 0 := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive lessOne fixedPoint coordinate.2 0
  exact Measure.infinitePi_map_eval _ (address, opened)

theorem independentInnovationLaw_independent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    iIndepFun (fun coordinate marks => marks coordinate)
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive lessOne fixedPoint coordinate.2 0
  exact iIndepFun_infinitePi (X := fun _ configuration => configuration) (fun _ => measurable_id)

theorem independentInnovationLaw_crosses (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∀ address opened, rule.network.crosses (marks (address, opened)) = opened := by
  apply ae_all_iff.mpr
  intro address
  apply ae_all_iff.mpr
  intro opened
  have crossing := history_law_latest_crosses rule p positive lessOne fixedPoint opened 0
  rw [← independentInnovationLaw_marginal rule p positive lessOne fixedPoint address opened] at crossing
  exact ae_of_ae_map (measurable_pi_apply (address, opened)).aemeasurable crossing

noncomputable def markedGenerationConfiguration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    (depth : ℕ) → List (Fin rule.edges) → Bool → Configuration (rule.generation depth).edges
  | 0, address, opened => marks (address, opened)
  | depth + 1, address, opened =>
      (rule.generationTopDecomposition depth).configuration.symm
        (substitutionConfigurationEquiv (fun edge =>
          markedGenerationConfiguration rule marks depth (address ++ [edge])
            (marks (address, opened) edge)))

theorem markedGenerationConfiguration_topCells (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    generationTopCells rule depth (markedGenerationConfiguration rule marks (depth + 1) address opened) =
      fun edge => markedGenerationConfiguration rule marks depth (address ++ [edge])
        (marks (address, opened) edge) := by
  simp [generationTopCells, generationTopCellsEquiv, markedGenerationConfiguration]

theorem markedGenerationConfiguration_crosses (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    (rule.generation depth).network.crosses
      (markedGenerationConfiguration rule marks depth address opened) = opened := by
  induction depth generalizing address opened with
  | zero => exact crossing address opened
  | succ depth inductionHypothesis =>
      rw [← generation_root_crosses, generationRootConfiguration,
        markedGenerationConfiguration_topCells]
      have coarse : (rule.generation depth).network.coarseConfiguration
          (fun edge => markedGenerationConfiguration rule marks depth (address ++ [edge])
            (marks (address, opened) edge)) = marks (address, opened) := by
        funext edge
        exact inductionHypothesis (address ++ [edge]) (marks (address, opened) edge)
      rw [coarse]
      exact crossing address opened

theorem markedGenerationConfiguration_root (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    generationRootConfiguration rule depth
        (markedGenerationConfiguration rule marks (depth + 1) address opened) =
      marks (address, opened) := by
  rw [generationRootConfiguration, markedGenerationConfiguration_topCells]
  funext edge
  exact markedGenerationConfiguration_crosses rule marks crossing depth _ _

theorem markedGenerationConfiguration_coarsens (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    rule.coarsenGeneration depth
        (markedGenerationConfiguration rule marks (depth + 1) address opened) =
      markedGenerationConfiguration rule marks depth address opened := by
  induction depth generalizing address opened with
  | zero =>
      exact markedGenerationConfiguration_root rule marks crossing 0 address opened
  | succ depth inductionHypothesis =>
      apply (generationTopCellsEquiv rule depth).injective
      change generationTopCells rule depth _ = generationTopCells rule depth _
      funext edge
      rw [generationTopCells_coarsen, markedGenerationConfiguration_topCells,
        markedGenerationConfiguration_topCells]
      exact inductionHypothesis (address ++ [edge]) (marks (address, opened) edge)

theorem marked_generations_coherent_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∀ address opened, configurationSequenceCoherent rule
        (fun depth => markedGenerationConfiguration rule marks depth address opened) := by
  filter_upwards [independentInnovationLaw_crosses rule p positive lessOne fixedPoint] with marks crossing
  intro address opened depth
  exact markedGenerationConfiguration_coarsens rule marks crossing depth address opened

end IGSIII.Chemical.Substitution

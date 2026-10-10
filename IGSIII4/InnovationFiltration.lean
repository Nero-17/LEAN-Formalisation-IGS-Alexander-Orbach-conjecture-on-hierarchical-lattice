import IGSIII.Probability.IndependentPrefix
import Mathlib.Probability.Martingale.Convergence

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Chemical.Substitution
open scoped Topology ProbabilityTheory

def innovationFiltration (rule : Rule) : Filtration ℕ
    (inferInstance : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges)) where
  seq := fun depth => ⨆ coordinate : List (Fin rule.edges) × Bool,
    ⨆ _ : coordinate.1.length < depth,
      MeasurableSpace.comap (fun marks => marks coordinate) inferInstance
  mono' := by
    intro first second ordered
    apply iSup_le
    intro coordinate
    apply iSup_le
    intro within
    exact le_iSup_of_le coordinate (le_iSup_of_le (within.trans_le ordered) le_rfl)
  le' := by
    intro depth
    apply iSup_le
    intro coordinate
    apply iSup_le
    intro _
    exact (measurable_pi_apply coordinate).comap_le

theorem innovationFiltration_exhausts (rule : Rule) :
    (⨆ depth, innovationFiltration rule depth) =
      (inferInstance : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges)) := by
  apply le_antisymm
  · exact iSup_le (fun depth => (innovationFiltration rule).le depth)
  · change (⨆ coordinate : List (Fin rule.edges) × Bool,
      MeasurableSpace.comap
        (fun marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges => marks coordinate)
        (inferInstance : MeasurableSpace (Configuration rule.edges))) ≤ _
    apply iSup_le
    intro coordinate
    apply le_iSup_of_le (coordinate.1.length + 1)
    exact le_iSup_of_le coordinate (le_iSup_of_le (Nat.lt_succ_self _) le_rfl)

theorem innovationFiltration_eq_prefix (rule : Rule) (depth : ℕ) :
    innovationFiltration rule depth = MeasurableSpace.comap
      (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
        (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}) =>
        marks coordinate.val) inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro coordinate
    apply iSup_le
    intro within
    exact MeasurableSpace.comap_le_comap_pi
      (g := fun (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth})
        (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) => marks coordinate.val)
      ⟨coordinate, within⟩
  · change MeasurableSpace.comap
      (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
        (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth}) =>
        marks coordinate.val)
      (⨆ coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth},
        MeasurableSpace.comap (fun values : {coordinate : List (Fin rule.edges) × Bool //
            coordinate.1.length < depth} → Configuration rule.edges => values coordinate)
          (inferInstance : MeasurableSpace (Configuration rule.edges))) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro coordinate
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le coordinate.val (le_iSup_of_le coordinate.property le_rfl)

theorem innovation_coordinate_measurable (rule : Rule) (depth : ℕ)
    (coordinate : List (Fin rule.edges) × Bool) (within : coordinate.1.length < depth) :
    Measurable[innovationFiltration rule depth] (fun marks => marks coordinate) := by
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le coordinate (le_iSup_of_le within le_rfl)

theorem markedGenerationConfiguration_prefix_measurable (rule : Rule) (total depth : ℕ)
    (address : List (Fin rule.edges)) (opened : Bool)
    (within : address.length + depth < total) :
    Measurable[innovationFiltration rule total]
      (fun marks => markedGenerationConfiguration rule marks depth address opened) := by
  letI : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges) :=
    innovationFiltration rule total
  induction depth generalizing address opened with
  | zero => exact innovation_coordinate_measurable rule total (address, opened) (by simpa using within)
  | succ depth inductionHypothesis =>
      have rootMeasurable := innovation_coordinate_measurable rule total (address, opened)
        (by change address.length < total; omega)
      have childMeasurable (edge : Fin rule.edges) : Measurable[innovationFiltration rule total]
          (fun marks => markedGenerationConfiguration rule marks depth (address ++ [edge])
            (marks (address, opened) edge)) := by
        have childWithin : (address ++ [edge]).length + depth < total := by
          simp only [List.length_append, List.length_singleton]
          omega
        have bothMeasurable : Measurable[innovationFiltration rule total]
            (fun marks childState => markedGenerationConfiguration rule marks depth (address ++ [edge]) childState) :=
          measurable_pi_lambda _ (fun childState => inductionHypothesis (address ++ [edge]) childState childWithin)
        have evaluatorMeasurable : Measurable (fun pair :
            (Bool → Configuration (rule.generation depth).edges) × Bool => pair.1 pair.2) :=
          measurable_of_finite _
        exact evaluatorMeasurable.comp
          (bothMeasurable.prodMk ((measurable_pi_apply edge).comp rootMeasurable))
      have functionalMeasurable : Measurable (fun cells : Fin rule.edges →
          Configuration (rule.generation depth).edges =>
        (rule.generationTopDecomposition depth).configuration.symm (substitutionConfigurationEquiv cells)) :=
        measurable_of_finite _
      have childrenMeasurable : Measurable[innovationFiltration rule total] (fun marks edge =>
          markedGenerationConfiguration rule marks depth (address ++ [edge])
            (marks (address, opened) edge)) := measurable_pi_lambda _ childMeasurable
      exact functionalMeasurable.comp childrenMeasurable

theorem innovation_condExp_converges (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint)) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      Tendsto (fun depth =>
        (condExp (innovationFiltration rule depth)
          (independentInnovationLaw rule probability positive belowOne fixedPoint) value) marks)
          atTop (𝓝 (value marks)) := by
  apply integrable.tendsto_ae_condExp (ℱ := innovationFiltration rule)
  rw [innovationFiltration_exhausts]
  exact measurable.stronglyMeasurable

end
end IGSIII4
